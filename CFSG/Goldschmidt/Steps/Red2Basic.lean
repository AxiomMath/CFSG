module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.Goldschmidt.Red2

open CFSG.Open CFSG.ComponentClassification

theorem goldschmidtSimpleType_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L') : goldschmidtSimpleType L := by
  unfold goldschmidtSimpleType at h ⊢
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ |
      ⟨p, f, hp, hodd, hf, h5, h8, ⟨e'⟩⟩ | ⟨k, hk, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hodd, hf, h5, h8, ⟨e.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, hk, (Nat.card_congr e.toEquiv).trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩))))

variable {G : Type*} [Group G]

theorem conj_eq_of_mul_inv_mem_centralizer {K : Subgroup G} {a t : G}
    (h : a * t⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    ∀ x ∈ K, a⁻¹ * x * a = t⁻¹ * x * t := by
  intro x hx
  have hc : x * (a * t⁻¹) = a * t⁻¹ * x := Subgroup.mem_centralizer_iff.mp h x hx
  calc a⁻¹ * x * a = t⁻¹ * ((a * t⁻¹)⁻¹ * (x * (a * t⁻¹))) * t := by group
    _ = t⁻¹ * x * t := by rw [hc]; group

theorem mul_inv_mem_centralizer_of_conj_eq {K : Subgroup G} {a t : G}
    (h : ∀ x ∈ K, a⁻¹ * x * a = t⁻¹ * x * t) : a * t⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  calc x * (a * t⁻¹) = a * (a⁻¹ * x * a) * t⁻¹ := by group
    _ = a * t⁻¹ * x := by rw [h x hx]; group

theorem sq_mem_centralizer_of_mul_inv_mem {K : Subgroup G} {a t : G} (ht : t ∈ K)
    (hc : a * t⁻¹ ∈ Subgroup.centralizer (K : Set G))
    (ha : a ^ 2 ∈ Subgroup.centralizer (K : Set G)) :
    t ^ 2 ∈ Subgroup.centralizer (K : Set G) := by
  have hct : t * (a * t⁻¹) = a * t⁻¹ * t := Subgroup.mem_centralizer_iff.mp hc t ht
  have heq : t ^ 2 = ((a * t⁻¹) ^ 2)⁻¹ * a ^ 2 := by
    have hcomm : Commute (a * t⁻¹) t := hct.symm
    have h1 : a = a * t⁻¹ * t := by group
    calc t ^ 2 = ((a * t⁻¹) ^ 2)⁻¹ * ((a * t⁻¹) ^ 2 * t ^ 2) := by group
      _ = ((a * t⁻¹) ^ 2)⁻¹ * a ^ 2 := by rw [← hcomm.mul_pow, ← h1]
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc 2)) ha

theorem sq_eq_one_of_mem_closure {X : Type*} [Group X] {B : Subgroup X}
    (hB : IsMulCommutative B) {s : Set X} (hs : ∀ t ∈ s, t ^ 2 = 1)
    (hBs : B = Subgroup.closure s) : ∀ y ∈ B, y ^ 2 = 1 := by
  intro y hy
  rw [hBs] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact one_pow 2
  | mul x z hx hz ihx ihz =>
    have hxz : x * z = z * x := by
      have := hB.is_comm.comm ⟨x, hBs ▸ hx⟩ ⟨z, hBs ▸ hz⟩
      exact congrArg Subtype.val this
    have hcomm : Commute x z := hxz
    rw [hcomm.mul_pow, ihx, ihz, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem exists_mem_inf_mul_inv_mem_centralizer [Finite G] (S : Sylow 2 G) {K : Subgroup G}
    (hKn : K.Normal) (hZ : IsPGroup 2 (Subgroup.center K)) {x k : G}
    (hx : x ∈ (S : Subgroup G)) (hk : k ∈ K)
    (hc : k⁻¹ * x ∈ Subgroup.centralizer (K : Set G)) :
    ∃ t ∈ (S : Subgroup G) ⊓ K, x * t⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hKn.isSubnormal
  have hTmem : ∀ h : K, h ∈ (T : Subgroup K) ↔ (h : G) ∈ (S : Subgroup G) := by
    intro h
    constructor
    · intro hh
      have hmem : (h : G) ∈ (T : Subgroup K).map K.subtype := ⟨h, hh, rfl⟩
      rw [hT] at hmem
      exact hmem.1
    · intro hh
      have hmem : (h : G) ∈ (T : Subgroup K).map K.subtype := by
        rw [hT]
        exact ⟨hh, h.2⟩
      obtain ⟨h', hh', hh'eq⟩ := hmem
      rwa [show h' = h from Subtype.ext hh'eq] at hh'
  set c := k⁻¹ * x with hcdef
  have hxkc : x = k * c := by rw [hcdef]; group
  have hcK : ∀ y ∈ K, y * c = c * y := fun y hy => Subgroup.mem_centralizer_iff.mp hc y hy
  have hkc : Commute k c := hcK k hk
  obtain ⟨m, hm⟩ := S.2 ⟨x, hx⟩
  have hxm : x ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hkm : k ^ 2 ^ m ∈ Subgroup.centralizer (K : Set G) := by
    have h1 : k ^ 2 ^ m * c ^ 2 ^ m = 1 := by rw [← hkc.mul_pow, ← hxkc, hxm]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc _)
  have hkmZ : (⟨k ^ 2 ^ m, K.pow_mem hk _⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hkm g g.2)
  obtain ⟨j, hj⟩ := hZ ⟨_, hkmZ⟩
  have hkj : k ^ 2 ^ (m + j) = 1 := by
    have h1 := congrArg (fun z : Subgroup.center K => ((z : K) : G)) hj
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    rw [pow_add, pow_mul, h1]
  set k' : K := ⟨k, hk⟩ with hk'def
  have hk'p : IsPGroup 2 (Subgroup.zpowers k') := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨m + j, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, SubgroupClass.coe_zpow, OneMemClass.coe_one, hk'def]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hkj, one_zpow]
  have hk'N : k' ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hTmem, hTmem]
    have hconj : ((k' * h * k'⁻¹ : K) : G) = x * (h : G) * x⁻¹ := by
      have hhc := hcK h h.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk'def]
      rw [hxkc]
      calc k * (h : G) * k⁻¹ = k * ((h : G) * c * c⁻¹) * k⁻¹ := by group
        _ = k * c * (h : G) * (k * c)⁻¹ := by rw [hhc]; group
    rw [hconj]
    constructor
    · intro hh
      exact S.mul_mem (S.mul_mem hx hh) (S.inv_mem hx)
    · intro hh
      have := S.mul_mem (S.mul_mem (S.inv_mem hx) hh) hx
      simpa [mul_assoc] using this
  have hk'T : k' ∈ (T : Subgroup K) := by
    have hmem : k' ∈ Subgroup.zpowers k' ⊓ (T : Subgroup K) := by
      rw [← IsPGroup.inf_normalizer_sylow hk'p T]
      exact ⟨Subgroup.mem_zpowers k', hk'N⟩
    exact hmem.2
  refine ⟨k, ⟨(hTmem k').mp hk'T, hk⟩, ?_⟩
  rw [hxkc, hkc.eq, mul_inv_cancel_right]
  exact hc

theorem component_le_centralizer [Finite G] {K L : Subgroup G} (hK : IsComponentOf K ⊤)
    (hL : IsComponentOf L ⊤) (hne : K ≠ L) : K ≤ Subgroup.centralizer (L : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp (LocalComponents.commute_of_ne K L hK hL hne)

theorem mem_centralizer_sSup {𝒦 : Set (Subgroup G)} {x : G}
    (hx : ∀ K ∈ 𝒦, x ∈ Subgroup.centralizer (K : Set G)) :
    x ∈ Subgroup.centralizer ((sSup 𝒦 : Subgroup G) : Set G) := by
  have hle : sSup 𝒦 ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sSup_le fun K hK y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (Subgroup.mem_centralizer_iff.mp (hx K hK) y hy).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hy) x rfl).symm

theorem exists_mem_iSup_mul_inv_mem_centralizer (𝒦 : Set (Subgroup G)) (h𝒦 : 𝒦.Finite)
    (hcomm : ∀ K ∈ 𝒦, ∀ L ∈ 𝒦, K ≠ L → K ≤ Subgroup.centralizer (L : Set G))
    (B : Subgroup G → Subgroup G) (hB : ∀ K ∈ 𝒦, B K ≤ K) (g : G)
    (hg : ∀ K ∈ 𝒦, ∃ x ∈ B K, g * x⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    ∃ y ∈ ⨆ K ∈ 𝒦, B K, ∀ K ∈ 𝒦, g * y⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  suffices key : ∀ F : Set (Subgroup G), F.Finite → F ⊆ 𝒦 →
      ∃ y ∈ ⨆ K ∈ F, B K, ∀ K ∈ F, g * y⁻¹ ∈ Subgroup.centralizer (K : Set G) from
    key 𝒦 h𝒦 subset_rfl
  intro F hF
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    exact fun _ => ⟨1, Subgroup.one_mem _, fun K hK => absurd hK (Set.notMem_empty K)⟩
  | @insert K' F hK'F hF ih =>
    intro hsub
    have hK' : K' ∈ 𝒦 := hsub (Set.mem_insert K' F)
    have hF𝒦 : F ⊆ 𝒦 := (Set.subset_insert K' F).trans hsub
    obtain ⟨y, hy, hyc⟩ := ih hF𝒦
    obtain ⟨x, hx, hxc⟩ := hg K' hK'
    have hyK' : y ∈ Subgroup.centralizer (K' : Set G) :=
      (iSup₂_le fun K hK => (hB K (hF𝒦 hK)).trans
        (hcomm K (hF𝒦 hK) K' hK' fun h => hK'F (h ▸ hK))) hy
    have hxy : x * y = y * x := Subgroup.mem_centralizer_iff.mp hyK' x (hB K' hK' hx)
    refine ⟨x * y, ?_, fun K hK => ?_⟩
    · rw [iSup_insert]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)
    · rcases Set.mem_insert_iff.mp hK with hKK' | hKF
      · rw [hKK', hxy, mul_inv_rev, ← mul_assoc]
        exact Subgroup.mul_mem _ hxc (Subgroup.inv_mem _ hyK')
      · rw [mul_inv_rev, ← mul_assoc]
        refine Subgroup.mul_mem _ (hyc K hKF) (Subgroup.inv_mem _ ?_)
        exact hcomm K' hK' K (hF𝒦 hKF) (fun h => hK'F (h ▸ hKF)) (hB K' hK' hx)

theorem mem_iSup_inf_centralizer (𝒦 : Set (Subgroup G)) (h𝒦 : 𝒦.Finite)
    (hnormal : ∀ K ∈ 𝒦, K.Normal)
    (hcomm : ∀ K ∈ 𝒦, ∀ L ∈ 𝒦, K ≠ L → K ≤ Subgroup.centralizer (L : Set G)) {z : G}
    (hz : z ∈ sSup 𝒦) (hzc : ∀ K ∈ 𝒦, z ∈ Subgroup.centralizer (K : Set G)) :
    z ∈ ⨆ K ∈ 𝒦, K ⊓ Subgroup.centralizer (K : Set G) := by
  suffices key : ∀ F : Set (Subgroup G), F.Finite → F ⊆ 𝒦 → ∀ z ∈ sSup F,
      (∀ K ∈ F, z ∈ Subgroup.centralizer (K : Set G)) →
      z ∈ ⨆ K ∈ F, K ⊓ Subgroup.centralizer (K : Set G) from key 𝒦 h𝒦 subset_rfl z hz hzc
  intro F hF
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    intro _ z hz _
    rw [sSup_empty, Subgroup.mem_bot] at hz
    rw [hz]
    exact Subgroup.one_mem _
  | @insert K' F hK'F hF ih =>
    intro hsub z hz hzc
    have hK' : K' ∈ 𝒦 := hsub (Set.mem_insert K' F)
    have hF𝒦 : F ⊆ 𝒦 := (Set.subset_insert K' F).trans hsub
    have := hnormal K' hK'
    rw [sSup_insert] at hz
    obtain ⟨k, hk, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hz
    have hwK' : w ∈ Subgroup.centralizer (K' : Set G) :=
      (sSup_le fun K hK => hcomm K (hF𝒦 hK) K' hK' fun h => hK'F (h ▸ hK)) hw
    have hkc : k ∈ Subgroup.centralizer (K' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 : h * (k * w) = k * w * h :=
        Subgroup.mem_centralizer_iff.mp (hzc K' (Set.mem_insert K' F)) h hh
      have h2 : h * w = w * h := Subgroup.mem_centralizer_iff.mp hwK' h hh
      calc h * k = h * (k * w) * w⁻¹ := by group
        _ = k * (w * h) * w⁻¹ := by rw [h1]; group
        _ = k * h := by rw [← h2]; group
    have hwF : ∀ K ∈ F, w ∈ Subgroup.centralizer (K : Set G) := by
      intro K hK
      have hkK : k ∈ Subgroup.centralizer (K : Set G) :=
        hcomm K' hK' K (hF𝒦 hK) (fun h => hK'F (h ▸ hK)) hk
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hkK) (hzc K (Set.mem_insert_of_mem K' hK))
      simpa using this
    rw [iSup_insert]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hk, hkc⟩)
      (Subgroup.mem_sup_right (ih hF𝒦 w hw hwF))

theorem eq_top_of_le_center_of_odd_index {D : Type*} [Group D] [Finite D]
    (hO : goldschmidtOddCore D = ⊥) (N : Subgroup D) [N.Normal] (hNZ : N ≤ Subgroup.center D)
    (hN2 : IsPGroup 2 N) (hodd : Odd N.index) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hN2
  have hcop : (Nat.card N).Coprime N.index := by
    rw [hr]
    exact Nat.Coprime.pow_left r (Nat.coprime_two_left.mpr hodd)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = N.index := by
    have h1 := hH.card_mul_card
    have h2 := N.card_mul_index
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hHn : H.Normal := by
    constructor
    intro h hh d
    obtain ⟨⟨⟨n, hn⟩, ⟨h', hh'⟩⟩, hd, -⟩ := Subgroup.IsComplement.existsUnique hH d
    simp only at hd
    rw [← hd]
    have hcen : (h' * h * h'⁻¹) * n = n * (h' * h * h'⁻¹) :=
      Subgroup.mem_center_iff.mp (hNZ hn) _
    have heq : n * h' * h * (n * h')⁻¹ = h' * h * h'⁻¹ := by
      calc n * h' * h * (n * h')⁻¹ = n * (h' * h * h'⁻¹) * n⁻¹ := by group
        _ = h' * h * h'⁻¹ := by rw [← hcen]; group
    rw [heq]
    exact H.mul_mem (H.mul_mem hh' hh) (H.inv_mem hh')
  have hHle : H ≤ goldschmidtOddCore D := le_sSup ⟨hHn, hHcard ▸ hodd⟩
  rw [hO, le_bot_iff] at hHle
  rw [hHle] at hH
  exact Subgroup.isComplement'_bot_right.mp hH

theorem goldschmidtOddCore_quotient_eq_bot_of_sup [Finite G] (E C : Subgroup G) [E.Normal]
    [C.Normal] (hO : goldschmidtOddCore G = ⊥) (hEC : E ⊔ C = ⊤)
    (hcomm : ∀ z ∈ E, z ∈ C → ∀ c ∈ C, c * z = z * c)
    (h2 : IsPGroup 2 (E ⊓ C : Subgroup G)) : goldschmidtOddCore (G ⧸ E) = ⊥ := by
  set O' := goldschmidtOddCore (G ⧸ E) with hO'def
  set Y : Subgroup G := O'.comap (QuotientGroup.mk' E) with hYdef
  have hYn : Y.Normal := (goldschmidtOddCore_normal _).comap _
  set D : Subgroup G := Y ⊓ C with hDdef
  have hDn : D.Normal := Subgroup.normal_inf_normal Y C
  set N : Subgroup D := E.subgroupOf D with hNdef
  have hNZ : N ≤ Subgroup.center D := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro d
    exact Subtype.ext (hcomm n hn n.2.2 d d.2.2)
  have hN2 : IsPGroup 2 N := by
    have hle : N.map D.subtype ≤ E ⊓ C := by
      rintro _ ⟨n, hn, rfl⟩
      exact ⟨hn, n.2.2⟩
    exact (h2.to_le hle).of_equiv (N.equivMapOfInjective D.subtype D.subtype_injective).symm
  set f : D →* G ⧸ E := (QuotientGroup.mk' E).comp D.subtype with hfdef
  have hker : f.ker = N := by
    ext d
    simp only [hfdef, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hNdef, Subgroup.mem_subgroupOf]
  have hrange : f.range ≤ O' := by
    rintro _ ⟨d, rfl⟩
    exact d.2.1
  have hodd : Odd N.index := by
    rw [← hker, Subgroup.index_ker]
    exact (OddCore.odd_card (G ⧸ E)).of_dvd_nat (Subgroup.card_dvd_of_le hrange)
  have hOD : goldschmidtOddCore D = ⊥ := by
    have h := OddCore.normal_intersection G D
    change (goldschmidtOddCore D).map D.subtype = D ⊓ goldschmidtOddCore G at h
    rw [hO, inf_bot_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp h
  have hNtop : N = ⊤ := eq_top_of_le_center_of_odd_index hOD N hNZ hN2 hodd
  have hDE : D ≤ E := by
    intro d hd
    have : (⟨d, hd⟩ : D) ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
    exact this
  have hYE : Y ≤ E := by
    intro y hy
    have hy' : y ∈ E ⊔ C := by rw [hEC]; exact Subgroup.mem_top y
    obtain ⟨e, he, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy'
    have heY : e ∈ Y := by
      change QuotientGroup.mk' E e ∈ O'
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff e).mpr he]
      exact O'.one_mem
    have hcY : c ∈ Y := by
      have := Y.mul_mem (Y.inv_mem heY) hy
      simpa using this
    exact E.mul_mem he (hDE ⟨hcY, hc⟩)
  rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective E) O']
  calc (O'.comap (QuotientGroup.mk' E)).map (QuotientGroup.mk' E)
      ≤ E.map (QuotientGroup.mk' E) := Subgroup.map_mono hYE
    _ = ⊥ := QuotientGroup.map_mk'_self E

end CFSG.Goldschmidt.Red2

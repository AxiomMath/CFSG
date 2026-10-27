module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointCase2Y
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointCase2Borel
import CFSG.LocalAnalysis.RankFourTheoremC.PPointEndgame
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointAbelian
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFusion

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

theorem eq_bot_or_eq_top_of_sq {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (A : AddSubgroup F)
    (hA : ∀ a : Fˣ, ∀ t ∈ A, (a : F) ^ 2 * t ∈ A) : A = ⊥ ∨ A = ⊤ := by
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.mpr fun y _ => ?_)
  obtain ⟨t, htA, ht0⟩ : ∃ t ∈ A, t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((AddSubgroup.eq_bot_iff_forall A).mpr hcon)
  have hsq : ∀ c : F, c ^ 2 * t ∈ A := by
    intro c
    by_cases hc : c = 0
    · simp [hc, A.zero_mem]
    · exact hA (Units.mk0 c hc) t htA
  have key : y = ((y / t + 1) / 2) ^ 2 * t - ((y / t - 1) / 2) ^ 2 * t := by
    field_simp
    ring
  rw [key]
  exact A.sub_mem (hsq _) (hsq _)

section Quotient

variable {G : Type} [Group G] [Finite G]

theorem case2Hyp_quotient (hS : D1Global G) {P : Sylow 3 G}
    (hPab : IsMulCommutative (P : Subgroup G)) {M : Subgroup G} (hMtop : M ≠ ⊤) {x : G}
    (hxM : x ∈ M) (hxo : orderOf x = 3)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) :
    Case2Hyp (M ⧸ primeComplementCore (G := M) 3)
      (QuotientGroup.mk' (primeComplementCore (G := M) 3) ⟨x, hxM⟩) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set O : Subgroup M := primeComplementCore (G := M) 3 with hO
  have hxo' : orderOf (⟨x, hxM⟩ : M) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  have hxo'' : orderOf (QuotientGroup.mk' O ⟨x, hxM⟩) = 3 :=
    orderOf_mk_of_coprime hp O (primeComplementCore_coprime 3) hxo'
  have hab : ∀ S : Sylow 3 (M ⧸ O), IsMulCommutative (S : Subgroup (M ⧸ O)) :=
    isMulCommutative_sylow_quotient (N := M) fun _ hQ => isMulCommutative_of_isPGroup hPab hQ
  exact
    { core_eq_bot := primeComplementCore_quotient_eq_bot 3
      catalog := (catalogSimpleSections_of_isKProper hS.kProper M hMtop).quotient O
      abelian := hab
      ne_one := fun h => by
        rw [h, orderOf_one] at hxo''
        omega
      pow_eq_one := by simpa only [hxo''] using pow_orderOf_eq_one (QuotientGroup.mk' O ⟨x, hxM⟩)
      weakClosed := fun Q hxQ g hg => weaklyClosed_map_mk hxo' hab
        (fun Q' hxQ' g' hg' => weakClosed_sylow hwc Q' hxQ' g' hg') Q hxQ g hg }

end Quotient

section Main

variable {G : Type} [Group G] [Finite G]

theorem BorelData3.card_QK {P : Sylow 3 G} {M : Subgroup G} {x : G} {n : ℕ}
    {f : GaloisField 3 n → G} {W : Subgroup G} (hB : BorelData3 P M x f W) :
    Nat.card hB.QK = 3 ^ n := by
  have hfinj : Function.Injective hB.fHom := fun a b hab =>
    Multiplicative.toAdd.injective (hB.f_inj hab)
  have h1 : Nat.card (Multiplicative (GaloisField 3 n)) = Nat.card hB.QK :=
    Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv
  rw [← h1, Nat.card_congr (Multiplicative.toAdd : Multiplicative (GaloisField 3 n) ≃ _)]
  exact GaloisField.card 3 n (by have := hB.three_le; omega)

theorem IsPPoint.conj_mem_sup_three {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hin : PPointThreeInputs) (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (h713 : GL83.I_7_13_1)
    (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x) {n : ℕ} {f : GaloisField 3 n → G}
    {W : Subgroup G} (hB : BorelData3 P M x f W) :
    ∀ m ∈ M, ∀ q ∈ hB.QK, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hPab := h.isMulCommutative_sylow_three hin hS hD1 hFC hloc
  have hwc := h.weaklyClosed_three hin hS hD1 hFC hloc
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hQKM : hB.QK ≤ M := hB.QK_le_P.trans hPM
  have hxM : x ∈ M := hPM hB.x_mem
  have hxo : orderOf x = 3 := h.elem.2.1
  have hMtop : M ≠ ⊤ := by
    have := hS.simple
    exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hloc.maxLocal.1
  have hxo' : orderOf (⟨x, hxM⟩ : M) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  have hbase := case2Hyp_quotient hS hPab hMtop hxM hxo hwc
  set O : Subgroup M := primeComplementCore (G := M) 3 with hO
  set π : M →* M ⧸ O := QuotientGroup.mk' O with hπ
  set xb : M ⧸ O := π ⟨x, hxM⟩ with hxb
  have hfM : ∀ t, f t ∈ M := fun t => hQKM (hB.f_mem_QK t)
  set ρ : GaloisField 3 n → M ⧸ O := fun t => π ⟨f t, hfM t⟩ with hρ
  set Z : Subgroup (M ⧸ O) := (hB.QK.subgroupOf M).map π with hZ
  have hZmem : ∀ z, z ∈ Z ↔ ∃ t, ρ t = z := by
    intro z
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨t, ht⟩ := hB.mem_QK.mp (mem_subgroupOf.mp hm)
      exact ⟨t, by simp only [hρ]; congr 1; exact Subtype.ext ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨⟨f t, hfM t⟩, mem_subgroupOf.mpr (hB.f_mem_QK t), rfl⟩
  have hρadd : ∀ s t, ρ (s + t) = ρ s * ρ t := by
    intro s t
    simp only [hρ]
    rw [← map_mul]
    congr 1
    exact Subtype.ext (hB.f_add s t)
  have hρ0 : ρ 0 = 1 := by
    simp only [hρ]
    have : (⟨f 0, hfM 0⟩ : M) = 1 := Subtype.ext hB.f_zero
    rw [this, map_one]
  have hρneg : ∀ t, ρ (-t) = (ρ t)⁻¹ := by
    intro t
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hρadd, neg_add_cancel, hρ0]
  have hρ3 : ∀ t, ρ t ^ 3 = 1 := by
    intro t
    simp only [hρ]
    rw [← map_pow]
    have : (⟨f t, hfM t⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hB.f_pow_three t)
    rw [this, map_one]
  have hZelem : IsElemAbelian 3 Z := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨s, hs⟩ := (hZmem a).mp a.2
      obtain ⟨t, ht⟩ := (hZmem b).mp b.2
      apply Subtype.ext
      show (a : M ⧸ O) * b = b * a
      rw [← hs, ← ht, ← hρadd, ← hρadd, add_comm]
    · obtain ⟨t, rfl⟩ := (hZmem z).mp hz
      exact hρ3 t
  have hZcard : Nat.card Z = 3 ^ n := by
    have hQp : IsPGroup 3 (hB.QK.subgroupOf M) := hB.QK_isPGroup.comap_subtype
    rw [hZ, card_map_mk_of_isPGroup hp O (primeComplementCore_coprime 3) hQp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQKM).toEquiv]
    exact hB.card_QK
  have hZc : Z ≤ centralizer ({xb} : Set (M ⧸ O)) := by
    intro z hz
    obtain ⟨t, rfl⟩ := (hZmem z).mp hz
    rw [mem_centralizer_singleton_iff]
    simp only [hρ, hxb]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hB.f_comm t)
  have hQK2 : 2 ≤ Open.pRank 3 hB.QK := by
    have := le_pRank_of_elemAbelian_card (p := 3) le_rfl hB.QK_isElemAbelian hB.card_QK
    have := hB.three_le
    omega
  have hQKN : normalizer (hB.QK : Set G) ≤ M :=
    normalizer_le_of_two_le_pRank hFC hloc hB.QK_isPGroup hQKM hQK2
  set S : Set (M ⧸ O) := {s | s * xb * s⁻¹ = xb ∧ ∀ z ∈ Z, s * z * s⁻¹ ∈ Z} with hS'
  have hStorus : ∀ a : (GaloisField 3 n)ˣ, ∃ s ∈ S, ∀ t,
      s * ρ t * s⁻¹ = ρ ((a : GaloisField 3 n) ^ 2 * t) := by
    intro a
    obtain ⟨g, hgx, hg⟩ := hB.torus a
    have hgN : g ∈ normalizer (hB.QK : Set G) := mem_normalizer_of_map_conj_le (by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨t, rfl⟩ := hB.mem_QK.mp hq
      show g * f t * g⁻¹ ∈ hB.QK
      rw [hg]
      exact hB.f_mem_QK _)
    have hgM : g ∈ M := hQKN hgN
    have hs : ∀ t, π ⟨g, hgM⟩ * ρ t * (π ⟨g, hgM⟩)⁻¹ = ρ ((a : GaloisField 3 n) ^ 2 * t) := by
      intro t
      simp only [hρ]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hg t)
    refine ⟨π ⟨g, hgM⟩, ⟨?_, fun z hz => ?_⟩, hs⟩
    · simp only [hxb]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hgx
    · obtain ⟨t, rfl⟩ := (hZmem z).mp hz
      rw [hs t]
      exact (hZmem _).mpr ⟨_, rfl⟩
  have h2 : (2 : GaloisField 3 n) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : GaloisField 3 n) = 0 := by exact_mod_cast h0
    have := (CharP.cast_eq_zero_iff (GaloisField 3 n) 3 2).mp h1
    omega
  have hirr : ∀ D : Subgroup (M ⧸ O), D ≤ Z → (∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D) →
      D = ⊥ ∨ D = Z := by
    intro D hDZ hDS
    let A : AddSubgroup (GaloisField 3 n) :=
      { carrier := {t | ρ t ∈ D}
        zero_mem' := by
          show ρ 0 ∈ D
          rw [hρ0]
          exact D.one_mem
        add_mem' := fun {s t} hs ht => by
          show ρ (s + t) ∈ D
          rw [hρadd]
          exact D.mul_mem hs ht
        neg_mem' := fun {t} ht => by
          show ρ (-t) ∈ D
          rw [hρneg]
          exact D.inv_mem ht }
    have hA : ∀ a : (GaloisField 3 n)ˣ, ∀ t ∈ A, (a : GaloisField 3 n) ^ 2 * t ∈ A := by
      intro a t ht
      obtain ⟨s, hsS, hs⟩ := hStorus a
      show ρ ((a : GaloisField 3 n) ^ 2 * t) ∈ D
      rw [← hs t]
      exact hDS s hsS _ ht
    rcases eq_bot_or_eq_top_of_sq h2 A hA with hA0 | hA1
    · left
      refine eq_bot_iff.mpr fun d hd => ?_
      obtain ⟨t, rfl⟩ := (hZmem d).mp (hDZ hd)
      have ht : t ∈ A := hd
      rw [hA0] at ht
      have ht0 : t = 0 := AddSubgroup.mem_bot.mp ht
      rw [ht0, hρ0]
      exact Subgroup.one_mem _
    · right
      refine le_antisymm hDZ fun z hz => ?_
      obtain ⟨t, rfl⟩ := (hZmem z).mp hz
      have ht : t ∈ A := by
        rw [hA1]
        trivial
      exact ht
  set Cx : Subgroup G := centralizer ({x} : Set G) with hCx
  set Ox : Subgroup G := GLBPrimeCore 3 Cx with hOx
  have hOxM : Ox ≤ M := h.primeCore_le hloc
  set Ob : Subgroup (M ⧸ O) := (Ox.subgroupOf M).map π with hOb
  have hObcop : ¬ 3 ∣ Nat.card Ob := by
    intro hdvd
    have h1 : Nat.card Ob ∣ Nat.card (Ox.subgroupOf M) :=
      Subgroup.card_dvd_of_surjective (f := π.subgroupMap (Ox.subgroupOf M))
        (π.subgroupMap_surjective _)
    have h2 : Nat.card (Ox.subgroupOf M) = Nat.card Ox :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOxM).toEquiv
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime 3 Cx) (h2 ▸ hdvd.trans h1)
  have hCy : centralizer ({xb} : Set (M ⧸ O)) ≤ ((M ⊓ Cx).subgroupOf M).map π :=
    (centralizer_mk_le_map hp hxo').trans (Subgroup.map_mono fun c
      (hc : c ∈ centralizer ({(⟨x, hxM⟩ : M)} : Set M)) => mem_subgroupOf.mpr
      ⟨c.2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩)
  have hnormO : centralizer ({xb} : Set (M ⧸ O)) ≤ normalizer (Ob : Set (M ⧸ O)) :=
    hCy.trans (map_subgroupOf_le_normalizer_map
      (fun c (hc : c ∈ M ⊓ Cx) => le_normalizer_glbPrimeCore 3 Cx hc.2) π)
  have hZO : Z ⊔ Ob = ((hB.QK ⊔ Ox).subgroupOf M).map π := by
    rw [Subgroup.subgroupOf_sup hQKM hOxM, Subgroup.map_sup]
  have hnormZO : centralizer ({xb} : Set (M ⧸ O)) ≤ normalizer ((Z ⊔ Ob : Subgroup (M ⧸ O)) :
      Set (M ⧸ O)) := by
    rw [hZO]
    exact hCy.trans (map_subgroupOf_le_normalizer_map hB.inf_centralizer_le_normalizer_QK_sup π)
  have hdata : Case2Data (M ⧸ O) xb Z S Ob :=
    { base := hbase
      isElemAbelian := hZelem
      card_eq := ⟨n, hB.three_le, hZcard⟩
      le_centralizer := hZc
      centralizes := fun s hs => hs.1
      normalizes := fun s hs => hs.2
      irreducible := hirr
      coprime := hObcop
      normalizes_O := hnormO
      normalizes_ZO := hnormZO }
  have hZp : Z ≤ CFSG.pCore 3 (M ⧸ O) := hdata.le_pCore hInn hWC h713
  have hPsyl : IsSylowOf 3 (P : Subgroup G) M := isSylowOf_iff.mpr ⟨hPM, P.isPGroup', fun hdvd =>
    P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hPM))⟩
  obtain ⟨R, hR⟩ : ∃ R : Sylow 3 (M ⧸ O), (R : Subgroup (M ⧸ O)) =
      ((P : Subgroup G).subgroupOf M).map π := by
    obtain ⟨-, hp', hdvd⟩ := isSylowOf_iff.1 (isSylowOf_top_map_mk hPsyl)
    rw [Subgroup.relIndex_top_right] at hdvd
    exact ⟨hp'.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩
  intro m hm q hq
  obtain ⟨t, rfl⟩ := hB.mem_QK.mp hq
  have hmq : m * f t * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm (hfM t)) (M.inv_mem hm)
  have hcj : π ⟨m * f t * m⁻¹, hmq⟩ = π ⟨m, hm⟩ * ρ t * (π ⟨m, hm⟩)⁻¹ := by
    simp only [hρ]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hpc : π ⟨m * f t * m⁻¹, hmq⟩ ∈ CFSG.pCore 3 (M ⧸ O) := by
    rw [hcj]
    exact (CFSG.pCore_normal (p := 3) (G := M ⧸ O)).conj_mem _ (hZp ((hZmem _).mpr ⟨t, rfl⟩)) _
  have hpR : π ⟨m * f t * m⁻¹, hmq⟩ ∈ (R : Subgroup (M ⧸ O)) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal R hpc
  rw [hR] at hpR
  obtain ⟨p', hp', hp'eq⟩ := hpR
  have hp'P : (p' : G) ∈ (P : Subgroup G) := mem_subgroupOf.mp hp'
  have hr : (p' : G)⁻¹ * (m * f t * m⁻¹) ∈ M := M.mul_mem (M.inv_mem p'.2) hmq
  have hker : π ⟨(p' : G)⁻¹ * (m * f t * m⁻¹), hr⟩ = 1 := by
    have e : (⟨(p' : G)⁻¹ * (m * f t * m⁻¹), hr⟩ : M) = p'⁻¹ * ⟨m * f t * m⁻¹, hmq⟩ := rfl
    rw [e, map_mul, map_inv, hp'eq, inv_mul_cancel]
  have hrO := mem_glbPrimeCore_of_mk_eq_one hr hker
  have : m * f t * m⁻¹ = (p' : G) * ((p' : G)⁻¹ * (m * f t * m⁻¹)) := by group
  rw [this]
  exact Subgroup.mul_mem _ (mem_sup_left hp'P) (mem_sup_right hrO)

end Main

end CFSG.LocalAnalysis.RankFourTheoremC

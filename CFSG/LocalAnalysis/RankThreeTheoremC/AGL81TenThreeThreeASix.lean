module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCore
import CFSG.LocalAnalysis.AGLEmbedding.SymThreeCentralExt
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup

theorem le_wSup_of_normal_symThree {Q : Type} [Group Q] {T : Subgroup Q} (hT : T.Normal)
    (e : ↥T ≃* Equiv.Perm (Fin 3)) : T ≤ wSup Q := by
  refine le_iSup₂ (f := fun T (_ : T ∈ {T : Subgroup Q | IsSubnormal T ⊤ ∧
    (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}) => T) T ⟨?_, Or.inr (Or.inl ⟨e⟩)⟩
  refine IsSubnormal.step le_top ?_ (IsSubnormal.refl ⊤)
  exact hT.subgroupOf ⊤

variable {A : Type} [Group A] [Finite A]

theorem threeASix_odd {Y P : Subgroup A} (hPY : P ≤ Y)
    (hZ : Nat.card (Subgroup.center ↥Y) = 3)
    (hA6 : Nonempty (↥Y ⧸ Subgroup.center ↥Y ≃* alternatingGroup (Fin 6)))
    (hS4 : Nonempty (↥((P.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))) ≃*
      Equiv.Perm (Fin 4))) :
    ¬ 2 ∣ P.relIndex Y ∧ ¬ 2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e6⟩ := hA6
  obtain ⟨e4⟩ := hS4
  set Z := Subgroup.center ↥Y with hZdef
  set ρ₀ : ↥P →* ↥Y ⧸ Z := (QuotientGroup.mk' Z).comp (inclusion hPY) with hρ₀
  have hrange : ρ₀.range = (P.subgroupOf Y).map (QuotientGroup.mk' Z) := by
    rw [hρ₀, MonoidHom.range_comp, inclusion_range]
  set ρ : ↥P →* Equiv.Perm (Fin 4) :=
    (e4.toMonoidHom.comp (MulEquiv.subgroupCongr hrange).toMonoidHom).comp ρ₀.rangeRestrict
    with hρ
  have hρs : Function.Surjective ρ := by
    refine (e4.surjective.comp (MulEquiv.subgroupCongr hrange).surjective).comp ?_
    exact ρ₀.rangeRestrict_surjective
  set C := ρ.ker with hCdef
  have hmemC : ∀ x : ↥P, x ∈ C ↔ (inclusion hPY x) ∈ Z := by
    intro x
    rw [hCdef, MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, MonoidHom.comp_apply]
    simp only [MulEquiv.coe_toMonoidHom, map_eq_one_iff _ (MulEquiv.injective _)]
    rw [Subtype.ext_iff, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one, hρ₀,
      MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hCc : ∀ c ∈ C, ∀ x : ↥P, c * x = x * c := by
    intro c hc x
    have h := (mem_center_iff.mp ((hmemC c).mp hc)) (inclusion hPY x)
    apply inclusion_injective hPY
    rw [map_mul, map_mul]
    exact h.symm
  have hCdvd : Nat.card C ∣ 3 := by
    have hle : C.map (inclusion hPY) ≤ Z := by
      rintro _ ⟨c, hc, rfl⟩
      exact (hmemC c).mp hc
    rw [← hZ, ← card_map_of_injective (inclusion_injective hPY)]
    exact card_dvd_of_le hle
  have hCodd : Odd (Nat.card C) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hCdvd with h | h <;> rw [h] <;> decide
  have hY : Nat.card Y = 1080 := by
    have hA : 2 * Nat.card (alternatingGroup (Fin 6)) = 720 := by
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    rw [card_eq_card_quotient_mul_card_subgroup Z, Nat.card_congr e6.toEquiv, hZ]
    omega
  have hP : Nat.card P = 24 * Nat.card C := by
    rw [card_eq_card_quotient_mul_card_subgroup C,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  refine ⟨?_, ?_⟩
  ·
    have h := card_mul_index (P.subgroupOf Y)
    rw [Nat.card_congr (subgroupOfEquivOfLe hPY).toEquiv, hP, hY] at h
    have h45 : Nat.card C * (P.subgroupOf Y).index = 45 := by
      rw [mul_assoc] at h
      omega
    intro h2
    have : 2 ∣ Nat.card C * (P.subgroupOf Y).index := dvd_mul_of_dvd_right h2 _
    rw [h45] at this
    norm_num at this
  ·
    set N : Subgroup ↥P := (CFSG.pCore 2 (Equiv.Perm (Fin 4))).comap ρ with hNdef
    have hNn : N.Normal := (CFSG.pCore_normal (p := 2) (G := Equiv.Perm (Fin 4))).comap ρ
    have hON : CFSG.pCore 2 ↥P ≤ N := by
      intro x hx
      have hle : (CFSG.pCore 2 ↥P).map ρ ≤ CFSG.pCore 2 (Equiv.Perm (Fin 4)) :=
        le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := ↥P)).map ρ hρs,
          (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).map ρ⟩
      exact hle ⟨x, hx, rfl⟩
    have hCN : C ≤ N := fun x hx => by
      rw [hNdef, mem_comap, (MonoidHom.mem_ker).mp hx]
      exact one_mem _
    obtain ⟨V⟩ : Nonempty (Sylow 2 ↥N) := inferInstance
    set V' : Subgroup ↥P := (V : Subgroup ↥N).map N.subtype with hV'
    have hV'N : V' ≤ N := map_subtype_le _
    have hV'2 : IsPGroup 2 V' := V.isPGroup'.map _
    have hCnorm : C.Normal := MonoidHom.normal_ker ρ
    have hNCV : N ≤ C ⊔ V' := by
      have hle : C ⊔ V' ≤ N := sup_le hCN hV'N
      have hdvd1 : (C ⊔ V').relIndex N ∣ V'.relIndex N := relIndex_dvd_of_le_left _ le_sup_right
      have hVi : V'.relIndex N = (V : Subgroup ↥N).index := by
        rw [relIndex, hV', CZeroLift.subgroupOf_map_subtype']
      have hodd1 : ¬ 2 ∣ V'.relIndex N := by rw [hVi]; exact V.not_dvd_index
      have hdvd2 : (C ⊔ V').relIndex N ∣ C.relIndex N := relIndex_dvd_of_le_left _ le_sup_left
      have hpow : IsPGroup 2 (↥N ⧸ C.subgroupOf N) := by
        have hsub : (C.subgroupOf N) = (ρ.comp N.subtype).ker := by
          ext x
          rw [mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply]
          rfl
        haveI : (C.subgroupOf N).Normal := hCnorm.subgroupOf N
        have e := (QuotientGroup.quotientMulEquivOfEq hsub).trans
          (QuotientGroup.quotientKerEquivRange (ρ.comp N.subtype))
        refine IsPGroup.of_equiv ?_ e.symm
        have hr : (ρ.comp N.subtype).range ≤ CFSG.pCore 2 (Equiv.Perm (Fin 4)) := by
          rintro _ ⟨x, rfl⟩
          exact x.2
        exact (CFSG.pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin 4))).to_le hr
      obtain ⟨m, hm⟩ := hpow.exists_card_eq
      have hCi : C.relIndex N = 2 ^ m := by
        rw [relIndex, index, hm]
      have hdvd3 : (C ⊔ V').relIndex N ∣ 2 ^ m := hCi ▸ hdvd2
      have hone : (C ⊔ V').relIndex N = 1 := by
        rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd3 with ⟨i, -, hi⟩
        rcases i with _ | i
        · simpa using hi
        · exact absurd (hi ▸ dvd_pow_self 2 (Nat.succ_ne_zero i) |>.trans hdvd1) hodd1
      exact relIndex_eq_one.mp hone
    have hCodd' : ∀ c ∈ C, ∀ a : ℕ, c ^ (2 ^ a) = 1 → c = 1 := by
      intro c hc a hca
      have hk : c ^ Nat.card C = 1 := by
        have h := pow_card_eq_one' (G := ↥C) (x := ⟨c, hc⟩)
        have h' := congrArg Subtype.val h
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h'
        exact h'
      have hg : orderOf c ∣ Nat.gcd (Nat.card C) (2 ^ a) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hca)
      have hcop : Nat.Coprime (Nat.card C) (2 ^ a) :=
        Nat.Coprime.pow_right _ (Odd.coprime_two_right hCodd)
      rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hg
      exact hg
    have h2elt : ∀ x ∈ N, (∃ a : ℕ, x ^ (2 ^ a) = 1) → x ∈ V' := by
      rintro x hx ⟨a, ha⟩
      have hx' : x ∈ V' ⊔ C := sup_comm C V' ▸ hNCV hx
      rw [← SetLike.mem_coe, mul_normal V' C] at hx'
      obtain ⟨v, hv, c, hc, rfl⟩ := hx'
      obtain ⟨b, hb⟩ := hV'2 ⟨v, hv⟩
      have hvb : v ^ (2 ^ b) = 1 := by simpa using congrArg Subtype.val hb
      have hcomm : Commute v c := (hCc c hc v).symm
      have h1 : (v * c) ^ (2 ^ (a + b)) = 1 := by
        rw [pow_add, pow_mul, ha, one_pow]
      have hv1 : v ^ (2 ^ (a + b)) = 1 := by
        rw [pow_add, mul_comm, pow_mul, hvb, one_pow]
      have hcv : c ^ (2 ^ (a + b)) = 1 := by
        rw [hcomm.mul_pow, hv1, one_mul] at h1
        exact h1
      show v * c ∈ V'
      rw [hCodd' c hc _ hcv, mul_one]
      exact hv
    have hV'n : V'.Normal := by
      refine ⟨fun v hv p => h2elt _ ?_ ?_⟩
      · exact hNn.conj_mem v (hV'N hv) p
      · obtain ⟨b, hb⟩ := hV'2 ⟨v, hv⟩
        refine ⟨b, ?_⟩
        rw [conj_pow, show v ^ 2 ^ b = 1 by simpa using congrArg Subtype.val hb]
        group
    have hV'O : V' ≤ CFSG.pCore 2 ↥P := le_sSup ⟨hV'n, hV'2⟩
    set q := QuotientGroup.mk' (CFSG.pCore 2 ↥P) with hq
    set f : ↥P ⧸ CFSG.pCore 2 ↥P →* Equiv.Perm (Fin 3) :=
      CFSG.AGLEmbedding.s4QuotientEquiv.toMonoidHom.comp
        (QuotientGroup.map _ _ ρ hON) with hf
    have hfs : Function.Surjective f := by
      refine CFSG.AGLEmbedding.s4QuotientEquiv.surjective.comp ?_
      intro y
      obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective _ y
      obtain ⟨x, rfl⟩ := hρs σ
      exact ⟨QuotientGroup.mk x, rfl⟩
    have hker : f.ker ≤ C.map q := by
      intro y hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥P) y
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ (MulEquiv.injective _), QuotientGroup.mk'_apply, QuotientGroup.map_mk,
        QuotientGroup.eq_one_iff] at hy
      have hxN : x ∈ N := hy
      have hx' : x ∈ C ⊔ CFSG.pCore 2 ↥P := (sup_le_sup_left hV'O C) (hNCV hxN)
      haveI : (CFSG.pCore 2 ↥P).Normal := CFSG.pCore_normal
      rw [← SetLike.mem_coe, mul_normal C (CFSG.pCore 2 ↥P)] at hx'
      obtain ⟨c, hc, o, ho, rfl⟩ := hx'
      refine ⟨c, hc, ?_⟩
      have hqo : q o = 1 := by rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact ho
      show q c = q (c * o)
      rw [map_mul, hqo, mul_one]
    have hfc : ∀ k ∈ f.ker, ∀ y, k * y = y * k := by
      intro k hk y
      obtain ⟨c, hc, rfl⟩ := hker hk
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥P) y
      rw [← map_mul, ← map_mul, hCc c hc x]
    have hfodd : Odd (Nat.card f.ker) := by
      have h1 : Nat.card f.ker ∣ Nat.card (C.map q) := card_dvd_of_le hker
      have h2 : Nat.card (C.map q) ∣ Nat.card C := card_map_dvd C q
      exact Odd.of_dvd_nat hCodd (h1.trans h2)
    obtain ⟨T, hTn, ⟨eT⟩, hTi⟩ := SymThreeCentralExt.exists_normal_symThree f hfs hfc hfodd
    intro h2
    exact hTi (h2.trans (index_dvd_of_le (le_wSup_of_normal_symThree hTn eT)))

variable (G : Type) [Group G] [Finite G]

theorem tenThreeThreeAt_four : TenThreeThreeAt G (fun M S L => NineThreeFour M S L) := by
  intro M H L _ _ hNH hMS hL _ h4 b _ _ _
  left
  have hLM : L ≤ M := hL.le
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  obtain ⟨-, hZ, hA6, -, hS4⟩ := h4
  rw [hNS] at hS4
  have hPY : barM M (H ⊓ L) ≤ barM M L := map_mono fun x hx => by
    rw [mem_subgroupOf] at hx ⊢
    exact hx.2
  obtain ⟨h1, h2⟩ := threeASix_odd hPY hZ hA6 hS4
  have hk : L ⊓ pCoreOf 2 M ≤ H := fun x hx =>
    (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (hMS hx.2)
  exact not_two_dvd_relIndex_jZero hLM hk h1 h2

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Structb
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Model
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Struct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

theorem l28iv_commutator_inner {L : Type} [Group L] [Finite L] (hL : IsRankThreeL28 L)
    (β γ : MulAut L) : ∃ l : L, MulAut.conj l = β * γ * β⁻¹ * γ⁻¹ := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I : Subgroup (MulAut L) := (MulAut.conj : L →* MulAut L).range with hI
  have hIn : I.Normal := ⟨by
    rintro _ ⟨g, rfl⟩ ψ
    refine ⟨ψ g, ?_⟩
    ext y
    simp [MulAut.conj_apply]⟩
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    refine Subgroup.mem_bot.mpr (l28m_eq_one_of_central hL fun y => ?_)
    have h := congrArg (fun α : MulAut L => α y) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h]
  have hAcard : Nat.card (MulAut L) = 1512 := l28m_card_mulAut hL
  have : Finite (MulAut L) := Nat.finite_of_card_ne_zero (by rw [hAcard]; norm_num)
  have hIcard : Nat.card I = 504 := by
    rw [hI, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      l28m_card hL]
  have hQcard : Nat.card (MulAut L ⧸ I) = 3 := by
    have h := I.index_mul_card
    rw [hIcard, hAcard] at h
    rw [← Subgroup.index_eq_card]
    omega
  have : Fact (Nat.card (MulAut L ⧸ I)).Prime := ⟨by rw [hQcard]; exact Nat.prime_three⟩
  have hcyc : IsCyclic (MulAut L ⧸ I) := isCyclic_of_prime_card rfl
  let π : MulAut L →* MulAut L ⧸ I := QuotientGroup.mk' I
  have hcomm : π β * π γ = π γ * π β := hcyc.commGroup.mul_comm _ _
  have h1 : π (β * γ * β⁻¹ * γ⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨l, hl⟩

variable {G : Type} [Group G] [Finite G]

theorem l28iv_hom_conj_mul_inv_mem (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) {m : G}
    (hmx : m * x * m⁻¹ ∈ zpowers x) {c : G} (hc : c ∈ centralizer ({x} : Set G))
    (hmc : m⁻¹ * c * m ∈ centralizer ({x} : Set G)) :
    l34Hom x J (⟨m⁻¹ * c * m, hmc⟩ * (⟨c, hc⟩ : ↥(centralizer ({x} : Set G)))⁻¹) ∈
      l34Img x J J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hJ.le_centralizer
  have hmC : ∀ d ∈ C, m⁻¹ * d * m ∈ C := by
    intro d hd
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmx
    have hdx : Commute d x := mem_centralizer_singleton_iff.mp hd
    have hdy : d * (m * x * m⁻¹) = (m * x * m⁻¹) * d := by
      rw [← hk]
      exact (Commute.zpow_right hdx k).eq
    refine mem_centralizer_singleton_iff.mpr ?_
    calc m⁻¹ * d * m * x = m⁻¹ * (d * (m * x * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * x * m⁻¹) * d) * m := by rw [hdy]
      _ = x * (m⁻¹ * d * m) := by group
  have hCmap : C.map (MulAut.conj m⁻¹).toMonoidHom = C := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨d, hd, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hmC d hd
    · rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective]
  set ψ : C ≃* C := ((MulAut.conj m⁻¹).subgroupMap C).trans (MulEquiv.subgroupCongr hCmap)
    with hψ
  have hψval : ∀ d : C, (ψ d : G) = m⁻¹ * d * m := fun d => by
    show ((MulAut.conj m⁻¹).subgroupMap C d : G) = m⁻¹ * d * m
    rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply, inv_inv]
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOψ : O.map ψ.toMonoidHom = O :=
    Subgroup.characteristic_iff_map_eq.mp (primeComplementCore_characteristic 3) ψ
  set ψb : C ⧸ O ≃* C ⧸ O := QuotientGroup.congr O O ψ hOψ with hψb
  set ρ : C →* C ⧸ O := QuotientGroup.mk' O with hρ
  have hψbρ : ∀ d, ψb (ρ d) = ρ (ψ d) := fun d => QuotientGroup.congr_mk' O O ψ hOψ d
  set L : Subgroup (C ⧸ O) := r1sBar x J with hL
  have hLn : L.Normal := r1sBar_normal_l28 hJ
  set L' : Subgroup (C ⧸ O) := L.map ψb.toMonoidHom with hL'
  have hL'n : L'.Normal := hLn.map ψb.toMonoidHom ψb.surjective
  have hLL : IsRankThreeL28 ↥L := r1sBar_isL28 hJ
  have hLcard : Nat.card L = 504 := l28m_card hLL
  have hLL' : L' = L := by
    have hcard : Nat.card L' = Nat.card L := Subgroup.card_map_of_injective ψb.injective
    have := hLn
    have := hL'n
    have hN : ((L' ⊓ L).subgroupOf L).Normal := inferInstance
    rcases l28s_bar_normal_eq_bot_or_eq_top hJ _ hN with h | h
    · exfalso
      have hdis : Disjoint L' L := by
        rw [Subgroup.disjoint_def]
        intro z hz1 hz2
        have hz : (⟨z, hz2⟩ : L) ∈ (L' ⊓ L).subgroupOf L :=
          Subgroup.mem_subgroupOf.mpr ⟨hz1, hz2⟩
        rw [h] at hz
        exact congrArg Subtype.val (Subgroup.mem_bot.mp hz)
      have hL'C : L' ≤ reducedCentralizerOfJ x J := by
        intro u hu
        rw [r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff]
        intro v hv
        exact (Subgroup.commute_of_normal_of_disjoint L' L hL'n hLn hdis u v hu hv).eq.symm
      have hcyc := l28_reducedCentralizer_isCyclic hS hU0 hp hM hgen hJ
      let _ := hcyc.commGroup
      have hLc : ∀ u ∈ L, ∀ v ∈ L, u * v = v * u := by
        intro u hu v hv
        apply ψb.injective
        rw [map_mul, map_mul]
        have hu' : ψb u ∈ reducedCentralizerOfJ x J := hL'C ⟨u, hu, rfl⟩
        have hv' : ψb v ∈ reducedCentralizerOfJ x J := hL'C ⟨v, hv, rfl⟩
        exact congrArg Subtype.val
          (mul_comm (⟨_, hu'⟩ : ↥(reducedCentralizerOfJ x J)) ⟨_, hv'⟩)
      have hper := r1sBar_perfect_l28 hJ
      have htop : _root_.commutator ↥L = ⊤ := Group.isPerfect_def.mp hper
      have hbot : _root_.commutator ↥L = ⊥ := by
        rw [_root_.commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro u _
        rw [mem_centralizer_iff]
        intro v _
        exact Subtype.ext (hLc _ v.2 _ u.2)
      have h1 : (⊤ : Subgroup ↥L) = ⊥ := htop.symm.trans hbot
      have h2 : Nat.card (⊤ : Subgroup ↥L) = 1 := by rw [h1, Subgroup.card_bot]
      rw [Subgroup.card_top, hLcard] at h2
      omega
    · have hle : L ≤ L' := fun z hz => by
        have hz' : (⟨z, hz⟩ : L) ∈ (L' ⊓ L).subgroupOf L := by
          rw [h]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hz').1
      exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  have hψbL : ∀ l ∈ L, ψb l ∈ L := fun l hl => by
    rw [← hLL']
    exact ⟨l, hl, rfl⟩
  have hψbL' : ∀ l ∈ L, ψb.symm l ∈ L := fun l hl => by
    rw [← hLL'] at hl
    obtain ⟨l₀, hl₀, hl₀e⟩ := hl
    have : ψb.symm l = l₀ := by
      rw [← hl₀e]
      exact ψb.symm_apply_apply l₀
    rw [this]
    exact hl₀
  set β : MulAut ↥L :=
    { toFun := fun l => ⟨ψb l, hψbL l l.2⟩
      invFun := fun l => ⟨ψb.symm l, hψbL' l l.2⟩
      left_inv := fun l => Subtype.ext (ψb.symm_apply_apply (l : C ⧸ O))
      right_inv := fun l => Subtype.ext (ψb.apply_symm_apply (l : C ⧸ O))
      map_mul' := fun a b => Subtype.ext (map_mul ψb (a : C ⧸ O) (b : C ⧸ O)) } with hβ
  set a : C ⧸ O := ρ ⟨c, hc⟩ with ha
  set γ : MulAut ↥L := MulAut.conjNormal a with hγ
  obtain ⟨l, hl⟩ := l28iv_commutator_inner hLL β γ
  set b : C ⧸ O := ψb a * a⁻¹ with hb
  have hbρ : b = ρ (⟨m⁻¹ * c * m, hmc⟩ * (⟨c, hc⟩ : C)⁻¹) := by
    rw [hb, ha, hψbρ, map_mul, map_inv]
    congr 2
    exact Subtype.ext (hψval _)
  have hact : ∀ v ∈ L, b * v * b⁻¹ = (l : C ⧸ O) * v * (l : C ⧸ O)⁻¹ := by
    intro v hv
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨v, hv⟩ : ↥L) : C ⧸ O)) hl
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    have e1 : ((γ.symm ⟨v, hv⟩ : ↥L) : C ⧸ O) = a⁻¹ * v * a := by
      rw [hγ]
      simp
    have e2 : ∀ w : ↥L, ((β w : ↥L) : C ⧸ O) = ψb w := fun w => rfl
    have e3 : ∀ w : ↥L, ((β.symm w : ↥L) : C ⧸ O) = ψb.symm w := fun w => rfl
    have e4 : ∀ w : ↥L, ((γ w : ↥L) : C ⧸ O) = a * w * a⁻¹ := fun w => by
      rw [hγ, MulAut.conjNormal_apply]
    rw [e2, e4, e3, e1] at h1
    rw [h1, hb]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    group
  have hD : (l : C ⧸ O)⁻¹ * b ∈ reducedCentralizerOfJ x J := by
    rw [r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff]
    intro v hv
    have h := hact v hv
    calc v * ((l : C ⧸ O)⁻¹ * b) = (l : C ⧸ O)⁻¹ * ((l : C ⧸ O) * v * (l : C ⧸ O)⁻¹) * b := by
          group
      _ = (l : C ⧸ O)⁻¹ * (b * v * b⁻¹) * b := by rw [h]
      _ = (l : C ⧸ O)⁻¹ * b * v := by group
  have hDn := l28_reducedCentralizer_normal hJ
  have hπ : l34Hom x J (⟨m⁻¹ * c * m, hmc⟩ * (⟨c, hc⟩ : C)⁻¹) =
      QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore (l : C ⧸ O) := by
    change QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore
      (ρ (⟨m⁻¹ * c * m, hmc⟩ * (⟨c, hc⟩ : C)⁻¹)) = _
    rw [← hbρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.normalCore_eq_self]
    rw [show b⁻¹ * (l : C ⧸ O) = ((l : C ⧸ O)⁻¹ * b)⁻¹ by group]
    exact inv_mem hD
  rw [hπ, l28s_img_J_eq]
  exact ⟨l, l.2, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

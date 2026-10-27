module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.GorensteinWalter Subgroup

theorem exists_conj_eq_of_pow_eq_one_psl_two_sq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ 2) {α : MulAut (PSL2 K)} {k : ℕ}
    (hα : α ^ (p ^ k) = 1) : ∃ y : PSL2 K, α = MulAut.conj y := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp, hp.odd_of_ne_two (by omega), by norm_num, hK⟩
  have hcard : 3 < Nat.card K := by rw [hK]; nlinarith
  have hinj := pGammaL2ToMulAutPSL2_injective K hodd hcard
  obtain ⟨γ, hγ⟩ := pGammaL2ToMulAutPSL2_surjective K hK hodd hcard α
  have hγp : γ ^ (p ^ k) = 1 := hinj (by rw [map_pow, hγ, hα, map_one])
  have hσ : SemidirectProduct.rightHom γ = 1 := by
    set σ := SemidirectProduct.rightHom γ with hσdef
    have h1 : σ ^ (p ^ k) = 1 := by rw [hσdef, ← map_pow, hγp, map_one]
    have h2 : σ ^ 2 = 1 := by
      have hc := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
      rw [← hc]
      exact pow_card_eq_one'
    have hcop : Nat.Coprime (p ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2))
  have hmem : γ ∈ (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact hσ
  obtain ⟨g, rfl⟩ := hmem
  rw [pGammaL2ToMulAutPSL2_inl] at hγ
  have hgp : g ^ (p ^ k) = 1 := by
    apply pgl2InnerAutPSL2_injective K hodd hcard
    rw [map_pow, hγ, hα, map_one]
  have hgH : g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
    CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_three _
      (by rw [pgl2_psl2Range_index_eq_two K hodd]; norm_num) hp (by omega)
      (hgp ▸ Subgroup.one_mem _)
  obtain ⟨y, rfl⟩ := hgH
  exact ⟨y, by rw [← hγ, pgl2InnerAutPSL2_toPGL]⟩

variable {G : Type} [Group G]

theorem isMulCommutative_of_isPGroup_of_mulEquiv_psl_two {p f : ℕ} [Fact p.Prime] {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = p ^ f) {L A : Subgroup G} (e : L ≃* PSL2 K)
    (hAL : A ≤ L) (hA : IsPGroup p A) : IsMulCommutative A := by
  have hA' : IsPGroup p ((A.subgroupOf L).map e.toMonoidHom) :=
    (hA.comap_subtype (K := L)).map e.toMonoidHom
  obtain ⟨S, hS⟩ := hA'.exists_le_sylow
  obtain ⟨φ⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hK S
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : e ⟨a, hAL a.2⟩ ∈ S := hS ⟨⟨a, hAL a.2⟩, a.2, rfl⟩
  have hb : e ⟨b, hAL b.2⟩ ∈ S := hS ⟨⟨b, hAL b.2⟩, b.2, rfl⟩
  have h := congrArg φ (mul_comm (φ.symm ⟨_, ha⟩) (φ.symm ⟨_, hb⟩))
  rw [map_mul, map_mul, φ.apply_symm_apply, φ.apply_symm_apply] at h
  have h2 : e ⟨a, hAL a.2⟩ * e ⟨b, hAL b.2⟩ = e ⟨b, hAL b.2⟩ * e ⟨a, hAL a.2⟩ :=
    congrArg Subtype.val h
  rw [← map_mul, ← map_mul] at h2
  have h3 := congrArg Subtype.val (e.injective h2)
  exact Subtype.ext h3

theorem eq_one_of_commute_of_mulEquiv_psl_two {K : Type} [Field K] [Finite K] {L : Subgroup G}
    (e : L ≃* PSL2 K) {l : G} (hl : l ∈ L) (hc : ∀ h ∈ L, h * l = l * h) : l = 1 := by
  have hcenter : e ⟨l, hl⟩ ∈ Subgroup.center (PSL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hc h h.2))
  rw [psl2_center_eq_bot, Subgroup.mem_bot] at hcenter
  exact congrArg Subtype.val (e.injective (hcenter.trans (map_one e).symm))

theorem exists_mem_conj_eq_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = p ^ 2) {L : Subgroup G} (e : L ≃* PSL2 K) {g : G}
    (hg : g ∈ normalizer (L : Set G)) {k : ℕ} (hgk : g ^ (p ^ k) = 1) :
    ∃ l ∈ L, ∀ h ∈ L, g * h * g⁻¹ = l * h * l⁻¹ := by
  let β : MulAut L := L.normalizerMonoidHom ⟨g, hg⟩
  have hβ : β ^ (p ^ k) = 1 := by
    have h1 : (⟨g, hg⟩ : normalizer (L : Set G)) ^ (p ^ k) = 1 :=
      Subtype.ext (by simpa using hgk)
    rw [← map_pow, h1, map_one]
  have hα : (MulAut.congr e β) ^ (p ^ k) = 1 := by rw [← map_pow, hβ, map_one]
  obtain ⟨y, hy⟩ := exists_conj_eq_of_pow_eq_one_psl_two_sq hp hp5 hK hα
  refine ⟨(e.symm y : L), (e.symm y).2, fun h hh => ?_⟩
  have hβy : β = MulAut.conj (e.symm y) := by
    apply (MulAut.congr e).injective
    rw [hy]
    ext z
    simp [MulAut.congr_apply]
  have := congrArg (fun f : MulAut L => ((f ⟨h, hh⟩ : L) : G)) hβy
  simpa [β] using this

end CFSG.LocalAnalysis.RankThreeTheoremC

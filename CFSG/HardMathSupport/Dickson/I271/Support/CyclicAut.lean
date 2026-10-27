module

public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicHH
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.GorensteinWalter

section PGL

variable {F : Type} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

noncomputable abbrev glToEnd' : GL (Fin 2) F ≃* (Module.End F (Fin 2 → F))ˣ :=
  Matrix.GeneralLinearGroup.toLin

theorem coe_glToEnd'_scalar (u : Fˣ) :
    ((glToEnd' (Matrix.GeneralLinearGroup.scalar (Fin 2) u) : (Module.End F (Fin 2 → F))ˣ) :
      Module.End F (Fin 2 → F)) = (u : F) • (1 : Module.End F (Fin 2 → F)) := by
  ext v i
  simp [glToEnd', Matrix.GeneralLinearGroup.coe_toLin, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem pow_prime_eq_self (hF : Nat.card F = p) (x : F) : x ^ p = x := by
  haveI : Fintype F := Fintype.ofFinite F
  rw [← hF, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem exists_scalar_of_mk_eq_one {g : GL (Fin 2) F} (h : Matrix.ProjGenLinGroup.mk g = 1) :
    ∃ s : Fˣ, g = Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
  have hg : g ∈ Matrix.ProjGenLinGroup.mk.ker := h
  rw [Matrix.ProjGenLinGroup.ker_mk, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨s, hs⟩ := hg
  exact ⟨s, hs.symm⟩

theorem mk_scalar (s : Fˣ) :
    Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) s) = 1 := by
  have : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ Matrix.ProjGenLinGroup.mk.ker := by
    rw [Matrix.ProjGenLinGroup.ker_mk, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨s, rfl⟩
  exact this

theorem pgl2_eq_bot_of_normalized (hF : Nat.card F = p) (hp5 : 5 ≤ p) [CharP F p]
    {û : Matrix.ProjGenLinGroup (Fin 2) F} (hû : û ^ p = 1) (hû1 : û ≠ 1)
    {T' : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)} (hcop : Nat.Coprime p (Nat.card T'))
    (hnorm : û ∈ Subgroup.normalizer (T' : Set (Matrix.ProjGenLinGroup (Fin 2) F))) : T' = ⊥ := by
  classical
  set π := (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* Matrix.ProjGenLinGroup (Fin 2) F) with hπ
  obtain ⟨g₀, hg₀⟩ := Matrix.ProjGenLinGroup.mk_surjective û
  obtain ⟨s, hs⟩ : ∃ s : Fˣ, g₀ ^ p = Matrix.GeneralLinearGroup.scalar (Fin 2) s :=
    exists_scalar_of_mk_eq_one (by rw [map_pow, hg₀, hû])
  set g : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹ * g₀ with hg
  have hscal : ∀ (a : Fˣ), (Matrix.GeneralLinearGroup.scalar (Fin 2) a) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
    intro a
    rw [← map_pow]
    congr 1
    exact Units.ext (pow_prime_eq_self hF (a : F))
  have hgp : g ^ p = 1 := by
    have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹) g₀ :=
      Matrix.GeneralLinearGroup.scalar_commute s⁻¹ g₀
    rw [hg, hc.mul_pow, hscal, hs, ← map_mul, inv_mul_cancel, map_one]
  have hπg : π g = û := by
    rw [hg, map_mul, hπ, mk_scalar, one_mul]
    exact hg₀
  have hg1 : g ≠ 1 := by
    intro h
    apply hû1
    rw [← hπg, h, map_one]
  set x : (Module.End F (Fin 2 → F))ˣ := glToEnd' g with hx
  have hxp : x ^ p = 1 := by rw [hx, ← map_pow, hgp, map_one]
  have hx1 : x ≠ 1 := fun h => hg1 (glToEnd'.injective (by rw [← hx, h, map_one]))
  set Tt : Subgroup (Module.End F (Fin 2 → F))ˣ :=
    (T'.comap π).map glToEnd'.toMonoidHom with hTt
  have hTp : ∀ g' ∈ Tt, ¬ p ∣ orderOf g' := by
    rintro _ ⟨g₁, hg₁, rfl⟩ hdvd
    have hord : orderOf (glToEnd'.toMonoidHom g₁) = orderOf g₁ := MulEquiv.orderOf_eq glToEnd' g₁
    rw [hord] at hdvd
    have hpos : orderOf g₁ ≠ 0 := (orderOf_pos g₁).ne'
    set h : GL (Fin 2) F := g₁ ^ (orderOf g₁ / p) with hh
    have hho : orderOf h = p := orderOf_pow_orderOf_div hpos hdvd
    have hπh : π h ∈ T' := by
      rw [hh, map_pow]
      exact T'.pow_mem hg₁ _
    have hπp : (π h) ^ p = 1 := by rw [← map_pow, ← hho, pow_orderOf_eq_one, map_one]
    have hdvd1 : orderOf (π h) ∣ p := orderOf_dvd_of_pow_eq_one hπp
    have hdvd2 : orderOf (π h) ∣ Nat.card T' := by
      have := orderOf_dvd_natCard (⟨π h, hπh⟩ : T')
      rwa [Subgroup.orderOf_mk] at this
    have hπ1 : π h = 1 :=
      orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
    obtain ⟨s', hs'⟩ := exists_scalar_of_mk_eq_one hπ1
    have hh1 : h = 1 := by
      have h1 : h ^ p = 1 := by rw [← hho, pow_orderOf_eq_one]
      rw [hs', hscal] at h1
      rw [hs', h1]
    rw [hh1, orderOf_one] at hho
    exact hp.out.one_lt.ne hho
  have hn : ∀ g' ∈ Tt, x * g' * x⁻¹ ∈ Tt := by
    rintro _ ⟨g₁, hg₁, rfl⟩
    refine ⟨g * g₁ * g⁻¹, ?_, by simp [hx]⟩
    show π (g * g₁ * g⁻¹) ∈ T'
    rw [map_mul, map_mul, map_inv, hπg]
    exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 hg₁
  have hscalar := scalar_of_normalized_unipotent hp5 x hxp hx1 Tt hTp hn
  rw [eq_bot_iff]
  intro τ hτ
  obtain ⟨g₁, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective τ
  obtain ⟨c, hc⟩ := hscalar (glToEnd' g₁) ⟨g₁, hτ, rfl⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := (glToEnd' g₁).isUnit
    rw [show ((glToEnd' g₁ : (Module.End F (Fin 2 → F))ˣ) : Module.End F (Fin 2 → F)) = 0 by
      simpa using hc] at this
    exact not_isUnit_zero this
  have : g₁ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) := by
    apply glToEnd'.injective
    apply Units.ext
    rw [coe_glToEnd'_scalar]
    simpa using hc
  rw [Subgroup.mem_bot, this, mk_scalar]

end PGL

section Aut

variable {F : Type} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

theorem conj_congr {G H : Type*} [Group G] [Group H] (ε : G ≃* H) (g : G) :
    MulAut.congr ε (MulAut.conj g) = MulAut.conj (ε g) := by
  ext x
  simp [MulAut.congr, MulAut.conj_apply]

theorem pgl2InnerAut_toPGL (hodd : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (u : PSL2 F) : pgl2InnerAutPSL2 F hodd hcard (Matrix.ProjectiveSpecialLinearGroup.toPGL u) =
      MulAut.conj u := by
  ext x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pgl2InnerAutPSL2_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem hh_psl2 (hF : Nat.card F = p) (hp5 : 5 ≤ p) (u₀ : PSL2 F) (hu : orderOf u₀ = p)
    (T : Subgroup (MulAut (PSL2 F))) (hcop : Nat.Coprime p (Nat.card T))
    (hnorm : MulAut.conj u₀ ∈ Subgroup.normalizer (T : Set (MulAut (PSL2 F)))) : T = ⊥ := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp.out, hp.out.odd_of_ne_two (by omega), le_rfl, by rw [hF, pow_one]⟩
  have hcard : 3 < Nat.card F := by omega
  have hbij := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hF hodd hcard
  set Ψ := pgl2InnerAutPSL2 F hodd hcard with hΨ
  set T' : Subgroup (PGL2 F) := T.comap Ψ with hT'
  have hmap : T'.map Ψ = T := Subgroup.map_comap_eq_self_of_surjective hbij.2 T
  have hcard' : Nat.card T' = Nat.card T := by
    have := Subgroup.card_map_of_injective (f := Ψ) (K := T') hbij.1
    rw [hmap] at this
    exact this.symm
  have hcop' : Nat.Coprime p (Nat.card T') := by rwa [hcard']
  set û : PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL u₀ with hû
  have hûp : û ^ p = 1 := by
    rw [hû, ← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  have hû1 : û ≠ 1 := by
    intro h
    have : u₀ = 1 := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (by rw [← hû, h, map_one])
    rw [this, orderOf_one] at hu
    exact hp.out.one_lt.ne hu
  have hΨû : Ψ û = MulAut.conj u₀ := pgl2InnerAut_toPGL hodd hcard u₀
  have hnorm' : û ∈ Subgroup.normalizer (T' : Set (PGL2 F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 hnorm (Ψ h)
    rw [hT', Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv, hΨû]
    exact this
  have hT'bot := pgl2_eq_bot_of_normalized hF hp5 hûp hû1 hcop' hnorm'
  rw [← hmap, hT'bot, Subgroup.map_bot]

theorem kdHallHigmanL2_holds :
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S] [Finite S] (F : Type) [Field F] [Finite F],
      Nat.card F = p → Nonempty (S ≃* StatedProj (StatedSL 2 F)) → ∀ u : S, orderOf u = p →
        ∀ T : Subgroup (MulAut S), Nat.Coprime p (Nat.card T) →
          MulAut.conj u ∈ Subgroup.normalizer (T : Set (MulAut S)) → T = ⊥ := by
  intro p hp hp5 S _ _ F _ _ hF ⟨e⟩ u hu T hcop hnorm
  haveI : Fact p.Prime := ⟨hp⟩
  let ε : PSL2 F ≃* S :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).trans e.symm
  set T₀ : Subgroup (MulAut (PSL2 F)) := T.map (MulAut.congr ε.symm).toMonoidHom with hT₀
  have hu₀ : orderOf (ε.symm u) = p := by rw [MulEquiv.orderOf_eq]; exact hu
  have hcard : Nat.card T₀ = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.congr ε.symm).injective
  have hnorm₀ : MulAut.conj (ε.symm u) ∈ Subgroup.normalizer (T₀ : Set (MulAut (PSL2 F))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have key : ∀ t' : MulAut (PSL2 F), t' ∈ T₀ ↔ MulAut.congr ε t' ∈ T := by
      intro t'
      rw [hT₀, Subgroup.mem_map_equiv]
      simp
    rw [key, key, map_mul, map_mul, map_inv, conj_congr]
    simpa using Subgroup.mem_normalizer_iff.1 hnorm (MulAut.congr ε t)
  have hT₀bot := hh_psl2 hF hp5 (ε.symm u) hu₀ T₀ (by rwa [hcard]) hnorm₀
  rw [eq_bot_iff]
  intro t ht
  have : (MulAut.congr ε.symm) t ∈ T₀ := ⟨t, ht, rfl⟩
  rw [hT₀bot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact (MulAut.congr ε.symm).injective (by rw [this, map_one])

end Aut

end CFSG.HardMathSupport.Dickson.I271

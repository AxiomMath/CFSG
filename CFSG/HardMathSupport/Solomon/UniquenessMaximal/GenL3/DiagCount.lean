module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Mono

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open CFSG.HardMathSupport.Timmesfeld.LinearRank CFSG.SectionRank.OddCover Matrix

variable {Fo : Type} [Field Fo]

@[expose] def ratioHom (Fo : Type) [Field Fo] : (Fin 3 → Foˣ) →* Foˣ × Foˣ where
  toFun d := (d 0 / d 2, d 1 / d 2)
  map_one' := by simp
  map_mul' a b := by
    ext <;> simp [Pi.mul_apply, div_mul_div_comm]

theorem ratioHom_apply (d : Fin 3 → Foˣ) : ratioHom Fo d = (d 0 / d 2, d 1 / d 2) := rfl

theorem diag_mem_of_card [Finite Fo] (w : Foˣ) (hw3 : w ^ 3 = 1)
    (U : Subgroup (GL (Fin 3) Fo)) (hZ : Subgroup.center (GL (Fin 3) Fo) ≤ U)
    (hdiag : ∀ g ∈ U, ∃ d : Fin 3 → Foˣ, g = diagHom 3 d)
    (hexp : ∀ g ∈ U, g ^ 3 ∈ Subgroup.center (GL (Fin 3) Fo))
    (hcard : Nat.card U = 9 * Nat.card (Subgroup.center (GL (Fin 3) Fo))) (c : Fin 3) :
    diagHom 3 (fun k : Fin 3 => if k = c then w else 1) ∈ U := by
  classical
  set T : (Fin 3 → Foˣ) →* GL (Fin 3) Fo := diagHom 3 with hT
  have hTinj : Function.Injective T := diagHom_injective 3
  set Z := Subgroup.center (GL (Fin 3) Fo) with hZdef
  set Ut : Subgroup (Fin 3 → Foˣ) := U.comap T with hUt
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hUtU : Nat.card Ut = Nat.card U := by
    refine Nat.card_congr (Equiv.ofBijective (fun d : Ut => (⟨T d, d.2⟩ : U)) ⟨?_, ?_⟩)
    · intro a b h
      exact Subtype.ext (hTinj (congrArg Subtype.val h))
    · intro u
      obtain ⟨d, hd⟩ := hdiag u u.2
      exact ⟨⟨d, by rw [hUt, Subgroup.mem_comap, ← hd]; exact u.2⟩, Subtype.ext hd.symm⟩
  set ψ : Ut →* Foˣ × Foˣ := (ratioHom Fo).comp Ut.subtype with hψ
  have hconst : ∀ x : Foˣ, T (fun _ => x) = Matrix.GeneralLinearGroup.scalar (Fin 3) x := fun x =>
    diagHom_const x
  have hker : Nat.card ψ.ker = Nat.card Z := by
    have hkerc : ∀ d : ψ.ker, ∃ x : Foˣ, ∀ i, (d : Ut).1 i = x := by
      intro d
      have h : ratioHom Fo ((d : Ut).1) = 1 := d.2
      rw [ratioHom_apply, Prod.mk_eq_one] at h
      refine ⟨(d : Ut).1 2, fun i => ?_⟩
      fin_cases i
      · exact div_eq_one.1 h.1
      · exact div_eq_one.1 h.2
      · rfl
    have hmem : ∀ d : ψ.ker, T (d : Ut).1 ∈ Z := by
      intro d
      obtain ⟨x, hx⟩ := hkerc d
      have : (d : Ut).1 = fun _ => x := funext hx
      rw [this, hconst, hZdef, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨x, rfl⟩
    refine Nat.card_congr (Equiv.ofBijective (fun d : ψ.ker => (⟨T (d : Ut).1, hmem d⟩ : Z))
      ⟨?_, ?_⟩)
    · intro a b h
      have := hTinj (congrArg Subtype.val h)
      exact Subtype.ext (Subtype.ext this)
    · rintro ⟨z, hz⟩
      rw [hZdef, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨x, rfl⟩ := hz
      have hzU : Matrix.GeneralLinearGroup.scalar (Fin 3) x ∈ U := by
        apply hZ
        rw [hZdef, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨x, rfl⟩
      refine ⟨⟨⟨fun _ => x, by rw [hUt, Subgroup.mem_comap, hconst]; exact hzU⟩, ?_⟩, ?_⟩
      · rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, Subgroup.coe_subtype, ratioHom_apply,
          Prod.mk_eq_one]
        simp
      · exact Subtype.ext (hconst x)
  have hrange : Nat.card ψ.range = 9 := by
    have hmul := Subgroup.card_ker_mul_card_range ψ
    rw [hker, hUtU, hcard] at hmul
    have : Nat.card Z * Nat.card ψ.range = Nat.card Z * 9 := by linarith
    exact Nat.eq_of_mul_eq_mul_left hZpos this
  set S : Subgroup Foˣ := rootsOfUnity 3 Fo with hS
  have hScard : Nat.card S ≤ 3 := card_rootsOfUnity (k := 3) (R := Fo)
  have hS3 : ∀ x : Foˣ, x ∈ S ↔ x ^ 3 = 1 := fun x => mem_rootsOfUnity 3 x
  have hcube : ∀ d : Ut, ∃ x : Foˣ, ∀ i, ((d : Ut).1 i) ^ 3 = x := by
    intro d
    have h1 : T (d : Ut).1 ∈ U := d.2
    have h2 := hexp _ h1
    rw [← map_pow, hZdef, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨x, hx⟩ := h2
    refine ⟨x, fun i => ?_⟩
    have : ((d : Ut).1 ^ 3) = fun _ => x := hTinj (by rw [hconst]; exact hx.symm)
    exact congrFun this i
  have hrS : ∀ y : ψ.range, y.1.1 ∈ S ∧ y.1.2 ∈ S := by
    rintro ⟨_, d, rfl⟩
    obtain ⟨x, hx⟩ := hcube d
    have hd : ∀ i j, ((d : Ut).1 i / (d : Ut).1 j) ^ 3 = 1 := fun i j => by
      rw [div_pow, hx, hx, div_self']
    exact ⟨(hS3 _).2 (hd 0 2), (hS3 _).2 (hd 1 2)⟩
  set f : ψ.range → S × S := fun y => (⟨y.1.1, (hrS y).1⟩, ⟨y.1.2, (hrS y).2⟩) with hf
  have hfinj : Function.Injective f := by
    intro a b h
    have h1 := congrArg (fun p : S × S => (p.1 : Foˣ)) h
    have h2 := congrArg (fun p : S × S => (p.2 : Foˣ)) h
    exact Subtype.ext (Prod.ext h1 h2)
  have hSS : Nat.card (S × S) ≤ Nat.card ψ.range := by
    rw [Nat.card_prod, hrange]
    nlinarith
  have hfbij : Function.Bijective f := hfinj.bijective_of_nat_card_le hSS
  have hwS : w ∈ S := (hS3 w).2 hw3
  have h1S : (1 : Foˣ) ∈ S := S.one_mem
  have hwiS : w⁻¹ ∈ S := S.inv_mem hwS
  set tgt : S × S :=
    match c with
    | 0 => (⟨w, hwS⟩, ⟨1, h1S⟩)
    | 1 => (⟨1, h1S⟩, ⟨w, hwS⟩)
    | 2 => (⟨w⁻¹, hwiS⟩, ⟨w⁻¹, hwiS⟩) with htgt
  obtain ⟨⟨y, hy⟩, hyt⟩ := hfbij.2 tgt
  obtain ⟨d, rfl⟩ := hy
  set vv : Fin 3 → Foˣ := fun k : Fin 3 => if k = c then w else 1 with hvv
  have hratio : ∀ k : Fin 3, (d : Ut).1 k / (d : Ut).1 2 = vv k / vv 2 := by
    have e0 := congrArg (fun p : S × S => (p.1 : Foˣ)) hyt
    have e1 := congrArg (fun p : S × S => (p.2 : Foˣ)) hyt
    simp only [hf, htgt, hψ, MonoidHom.comp_apply, Subgroup.coe_subtype, ratioHom_apply] at e0 e1
    intro k
    fin_cases c <;> fin_cases k <;> simp_all
  have hdv : vv = fun k => (d : Ut).1 k * ((d : Ut).1 2)⁻¹ * vv 2 := by
    funext k
    rw [← div_eq_mul_inv, hratio k, div_mul_cancel]
  have hscal : Matrix.GeneralLinearGroup.scalar (Fin 3) (((d : Ut).1 2)⁻¹ * vv 2) ∈ U := by
    apply hZ
    rw [hZdef, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have : T vv = T (d : Ut).1 * Matrix.GeneralLinearGroup.scalar (Fin 3) (((d : Ut).1 2)⁻¹ * vv 2) := by
    rw [← hconst, ← map_mul]
    congr 1
    rw [hdv]
    funext k
    simp [mul_assoc]
  show T vv ∈ U
  rw [this]
  exact U.mul_mem d.2 hscal

theorem exists_conj_diag [Finite Fo] (w : Foˣ) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (U : Subgroup (GL (Fin 3) Fo)) (hZ : Subgroup.center (GL (Fin 3) Fo) ≤ U)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hexp : ∀ g ∈ U, g ^ 3 ∈ Subgroup.center (GL (Fin 3) Fo))
    (hcard : Nat.card U = 9 * Nat.card (Subgroup.center (GL (Fin 3) Fo))) :
    ∃ m : GL (Fin 3) Fo, ∀ c : Fin 3, m⁻¹ * diagHom 3 (fun k : Fin 3 => if k = c then w else 1) * m
      ∈ U := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : 3 ∣ Nat.card Foˣ := by
    have h3 : orderOf w = 3 := orderOf_eq_prime hw3 hw1
    rw [← h3]
    exact orderOf_dvd_natCard w
  have hPg : IsPGroup 3 (U.map (QuotientGroup.mk' (Subgroup.center (GL (Fin 3) Fo)))) := by
    rintro ⟨x, g, hg, rfl⟩
    refine ⟨1, ?_⟩
    apply Subtype.ext
    show ((QuotientGroup.mk' (Subgroup.center (GL (Fin 3) Fo))) g) ^ 3 ^ 1 = 1
    rw [pow_one, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hexp g hg
  obtain ⟨m, hm⟩ := exists_conj_into_mono hF3 U hPg
  set cm : GL (Fin 3) Fo →* GL (Fin 3) Fo := (MulAut.conj m).toMonoidHom with hcm
  have hcmapp : ∀ g, cm g = m * g * m⁻¹ := fun g => rfl
  have hcmZ : ∀ z ∈ Subgroup.center (GL (Fin 3) Fo), cm z = z := by
    intro z hz
    rw [hcmapp, Subgroup.mem_center_iff.1 hz m, mul_assoc, mul_inv_cancel, mul_one]
  set U' : Subgroup (GL (Fin 3) Fo) := U.map cm with hU'
  have hU'M : U' ≤ (monoHom 3 Fo).range := by
    rintro _ ⟨g, hg, rfl⟩
    exact hm g hg
  have hZ' : Subgroup.center (GL (Fin 3) Fo) ≤ U' := fun z hz => ⟨z, hZ hz, hcmZ z hz⟩
  have hcomm' : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hexp' : ∀ g ∈ U', g ^ 3 ∈ Subgroup.center (GL (Fin 3) Fo) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hcmZ _ (hexp a ha)]
    exact hexp a ha
  have hcard' : Nat.card U' = 9 * Nat.card (Subgroup.center (GL (Fin 3) Fo)) := by
    rw [hU', Subgroup.card_map_of_injective (MulAut.conj m).injective, hcard]
  have hdiag := mono_diag_of_comm U' hU'M hcomm' hexp' hcard'
  refine ⟨m, fun c => ?_⟩
  obtain ⟨g, hg, hgd⟩ := diag_mem_of_card w hw3 U' hZ' hdiag hexp' hcard' c
  have : m⁻¹ * diagHom 3 (fun k : Fin 3 => if k = c then w else 1) * m = g := by
    rw [← hgd, hcmapp]
    group
  rw [this]
  exact hg

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

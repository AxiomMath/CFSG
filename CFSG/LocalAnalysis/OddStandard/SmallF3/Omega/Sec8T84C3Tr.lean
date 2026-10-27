module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

private def emb {G : Type} [Group G] {E B : Subgroup G} (hBE : B ≤ E) (b : ↥B) : ↥E :=
  ⟨(b : G), hBE b.2⟩

private lemma emb_mul {G : Type} [Group G] {E B : Subgroup G} (hBE : B ≤ E) (b₁ b₂ : ↥B) :
    emb hBE (b₁ * b₂) = emb hBE b₁ * emb hBE b₂ := rfl

private def rfun {G : Type} [Group G] {E B : Subgroup G} (hBE : B ≤ E)
    (a : MulAut ↥E) (ha : ∀ e : ↥E, (e : G) ∈ B → (a e : G) ∈ B) (b : ↥B) : ↥B :=
  ⟨(a (emb hBE b) : G), ha (emb hBE b) b.2⟩

private lemma preserves_B {G : Type} [Group G] {E B : Subgroup G} (u : MulAut ↥E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (A : Subgroup (MulAut ↥E)) (hAu : ∀ a ∈ A, a * u = u * a) (a : ↥A) :
    ∀ e : ↥E, (e : G) ∈ B → (((a : MulAut ↥E) e : ↥E) : G) ∈ B := by
  intro e he
  have hcomm := hAu (a : MulAut ↥E) a.2
  have happ : (a : MulAut ↥E) (u e) = u ((a : MulAut ↥E) e) := by
    have h := congrArg (fun f : MulAut ↥E => f e) hcomm
    simpa [MulAut.mul_apply] using h
  have hue : u e = e := (hfix e).mpr he
  have hfixa : u ((a : MulAut ↥E) e) = (a : MulAut ↥E) e := by
    rw [← happ, hue]
  simpa using (hfix ((a : MulAut ↥E) e)).mp hfixa

private noncomputable def resAut {G : Type} [Group G] {E B : Subgroup G}
    (u : MulAut ↥E) (hBE : B ≤ E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (A : Subgroup (MulAut ↥E)) (hAu : ∀ a ∈ A, a * u = u * a) (a : ↥A) : MulAut ↥B :=
  MulEquiv.mk'
    { toFun := rfun hBE (a : MulAut ↥E) (preserves_B u hfix A hAu a)
      invFun := rfun hBE ((a⁻¹ : ↥A) : MulAut ↥E) (preserves_B u hfix A hAu a⁻¹)
      left_inv := by
        intro b
        apply Subtype.ext
        have hcancel : ((a⁻¹ : ↥A) : MulAut ↥E) * (a : MulAut ↥E) = 1 := by
          have h : (a⁻¹ * a : ↥A) = 1 := inv_mul_cancel a
          have := congrArg (fun x : ↥A => (x : MulAut ↥E)) h
          simpa using this
        have hcancel' : ((a⁻¹ : ↥A) : MulAut ↥E) ((a : MulAut ↥E) (emb hBE b)) =
            emb hBE b := by
          have := congrArg (fun f : MulAut ↥E => f (emb hBE b)) hcancel
          simpa [MulAut.mul_apply] using this
        change (((a⁻¹ : ↥A) : MulAut ↥E) ((a : MulAut ↥E) (emb hBE b)) : G) =
          (emb hBE b : G)
        rw [hcancel']
      right_inv := by
        intro b
        apply Subtype.ext
        have hcancel : (a : MulAut ↥E) * ((a⁻¹ : ↥A) : MulAut ↥E) = 1 := by
          have h : (a * a⁻¹ : ↥A) = 1 := mul_inv_cancel a
          have := congrArg (fun x : ↥A => (x : MulAut ↥E)) h
          simpa using this
        have hcancel' : (a : MulAut ↥E) (((a⁻¹ : ↥A) : MulAut ↥E) (emb hBE b)) =
            emb hBE b := by
          have := congrArg (fun f : MulAut ↥E => f (emb hBE b)) hcancel
          simpa [MulAut.mul_apply] using this
        change (((a : ↥A) : MulAut ↥E) (((a⁻¹ : ↥A) : MulAut ↥E) (emb hBE b)) : G) =
          (emb hBE b : G)
        rw [hcancel'] }
    (fun b₁ b₂ => by
      apply Subtype.ext
      change (((a : MulAut ↥E) (emb hBE (b₁ * b₂))) : G) =
        ((((a : MulAut ↥E) (emb hBE b₁)) * ((a : MulAut ↥E) (emb hBE b₂))) : G)
      rw [emb_mul]
      exact congrArg Subtype.val (map_mul (a : MulAut ↥E) (emb hBE b₁) (emb hBE b₂)))

private noncomputable def resHom {G : Type} [Group G] {E B : Subgroup G}
    (u : MulAut ↥E) (hBE : B ≤ E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (A : Subgroup (MulAut ↥E)) (hAu : ∀ a ∈ A, a * u = u * a) : ↥A →* MulAut ↥B :=
  MonoidHom.mk' (fun a => resAut u hBE hfix A hAu a) (fun a₁ a₂ => by
    ext b
    change ((((a₁ : ↥A) : MulAut ↥E) * ((a₂ : ↥A) : MulAut ↥E)) (emb hBE b) : G) =
      ((((a₁ : ↥A) : MulAut ↥E) (((a₂ : ↥A) : MulAut ↥E) (emb hBE b))) : G)
    rw [MulAut.mul_apply])

private lemma resHom_coe {G : Type} [Group G] {E B : Subgroup G}
    (u : MulAut ↥E) (hBE : B ≤ E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (A : Subgroup (MulAut ↥E)) (hAu : ∀ a ∈ A, a * u = u * a) (a : ↥A) (b : ↥B) :
    ((resHom u hBE hfix A hAu a) b : G) = ((a : MulAut ↥E) (emb hBE b) : G) := rfl

private lemma resHom_injective {G : Type} [Group G] {E B : Subgroup G}
    (u : MulAut ↥E) (hBE : B ≤ E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (A : Subgroup (MulAut ↥E)) (hAu : ∀ a ∈ A, a * u = u * a)
    (hAf : ∀ a ∈ A, (∀ e : ↥E, (e : G) ∈ B → a e = e) → a = 1) :
    Function.Injective (resHom u hBE hfix A hAu) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply Subtype.ext
  refine hAf (a : MulAut ↥E) a.2 (fun e he => ?_)
  have hb : (resHom u hBE hfix A hAu a) (⟨(e : G), he⟩ : ↥B) = (⟨(e : G), he⟩ : ↥B) := by
    rw [ha, MulAut.one_apply]
  have hcoe := congrArg Subtype.val hb
  have hemb : emb hBE (⟨(e : G), he⟩ : ↥B) = e := Subtype.ext rfl
  exact Subtype.ext (by simpa [resHom_coe, hemb] using hcoe)

theorem trans_of_factA5 (hA5 : Sec8T84FactA5) {G : Type} [Group G] (E B : Subgroup G)
    (hB : IsElemAb2 B 4) (hBE : B ≤ E) (u : MulAut ↥E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (A H : Subgroup (MulAut ↥E)) (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6)))
    (hAu : ∀ a ∈ A, a * u = u * a)
    (hAf : ∀ a ∈ A, (∀ e : ↥E, (e : G) ∈ B → a e = e) → a = 1) (hAH : A ≤ H) :
    ∀ x : ↥E, (x : G) ∈ B → x ≠ 1 → ∀ y : ↥E, (y : G) ∈ B → y ≠ 1 → ∃ a ∈ H, a x = y := by
  have hinj := resHom_injective u hBE hfix A hAu hAf
  have hisoRange :
      Nonempty (↥(resHom u hBE hfix A hAu).range ≃* alternatingGroup (Fin 6)) :=
    ⟨(MonoidHom.ofInjective hinj).symm.trans hA.some⟩
  obtain ⟨H5, hH5le, _hH5iso, hH5trans⟩ :=
    hA5 G B hB (resHom u hBE hfix A hAu).range hisoRange
  intro x hx hx1 y hy hy1
  let x' : ↥B := ⟨(x : G), hx⟩
  let y' : ↥B := ⟨(y : G), hy⟩
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hx1
    apply Subtype.ext
    exact congrArg (fun z : ↥B => (z : G)) h
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hy1
    apply Subtype.ext
    exact congrArg (fun z : ↥B => (z : G)) h
  obtain ⟨h, hhh, hhxy⟩ := hH5trans x' hx'1 y' hy'1
  have hh : h ∈ (resHom u hBE hfix A hAu).range := hH5le hhh
  obtain ⟨a, haeq⟩ := MonoidHom.mem_range.mp hh
  refine ⟨a, hAH a.2, ?_⟩
  have hresx : (resHom u hBE hfix A hAu a) x' = y' := by rw [haeq, hhxy]
  have hcoe := congrArg Subtype.val hresx
  have hcoe' : (((a : MulAut ↥E) x : ↥E) : G) = (y : G) := by
    change ((resHom u hBE hfix A hAu a) x' : G) = (y' : G)
    exact hcoe
  exact Subtype.ext hcoe'

end C10

end CFSG.OddStandard.SmallF3.Omega

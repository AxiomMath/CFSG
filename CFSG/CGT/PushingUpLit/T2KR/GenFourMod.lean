module

public import CFSG.CGT.PushingUpLit.T2KR.MMCoord

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

theorem card_ringEquiv_le (n : ℕ) (hn : n ≠ 0) :
    Nat.card (GaloisField 2 n ≃+* GaloisField 2 n) ≤ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card (GaloisField 2 n ≃+* GaloisField 2 n) ≤
      Nat.card Gal(GaloisField 2 n/ZMod 2) :=
    Nat.card_le_card_of_injective (toGal n) (toGal_injective n)
  have : Fintype Gal(GaloisField 2 n/ZMod 2) := Fintype.ofFinite _
  have h2 : Nat.card Gal(GaloisField 2 n/ZMod 2) = n := by
    rw [IsGalois.card_aut_eq_finrank (ZMod 2) (GaloisField 2 n), GaloisField.finrank 2 hn]
  omega

section SL2

variable {F : Type} [Field F]

theorem not_commute_unipotent {σ : F ≃+* F} (hσ : σ ≠ 1) {a : Equiv.Perm (Fin 2 → F)}
    (ha : IsSemilinearWith a σ) (hadd : ∀ x y, a (x + y) = a x + a y)
    (hcomm : ∀ t : F, slPerm F (CFSG.SL2MinimalFaithful.unipotent t) * a =
      a * slPerm F (CFSG.SL2MinimalFaithful.unipotent t)) : False := by
  have key : ∀ t : F, ∀ w : Fin 2 → F, a (slPerm F (CFSG.SL2MinimalFaithful.unipotent t) w) =
      slPerm F (CFSG.SL2MinimalFaithful.unipotent t) (a w) := fun t w => by
    have := congrArg (fun p : Equiv.Perm (Fin 2 → F) => p w) (hcomm t)
    exact this.symm
  have hu : ∀ (t : F) (v : Fin 2 → F), slPerm F (CFSG.SL2MinimalFaithful.unipotent t) v =
      ![v 0 + t * v 1, v 1] := fun t v => smul_unipotent_vec t v
  obtain ⟨e₀, he₀⟩ : ∃ e : Fin 2 → F, e = ![1, 0] := ⟨_, rfl⟩
  obtain ⟨e₁, he₁⟩ : ∃ e : Fin 2 → F, e = ![0, 1] := ⟨_, rfl⟩
  have he00 : e₀ 0 = 1 := by simp [he₀]
  have he01 : e₀ 1 = 0 := by simp [he₀]
  have he10 : e₁ 0 = 0 := by simp [he₁]
  have he11 : e₁ 1 = 1 := by simp [he₁]
  have hue1 : ∀ t : F, slPerm F (CFSG.SL2MinimalFaithful.unipotent t) e₁ = e₁ + t • e₀ := by
    intro t
    rw [hu]
    ext i
    fin_cases i <;> simp [he00, he01, he10, he11]
  have h1 : ∀ t : F, (σ t * (a e₀) 0 = t * (a e₁) 1) ∧ (t = 0 ∨ (a e₀) 1 = 0) := by
    intro t
    have h := key t e₁
    rw [hue1, hadd, ha t e₀, hu] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    exact ⟨h0, h1⟩
  have hμ : (a e₀) 0 = (a e₁) 1 := by
    have := (h1 1).1
    simpa using this
  have hμ0 : (a e₁) 1 ≠ 0 := by
    intro h0
    have hz : a e₀ = 0 := by
      ext i
      fin_cases i
      · simpa [h0] using hμ
      · rcases (h1 1).2 with h | h
        · exact absurd h one_ne_zero
        · simpa using h
    have h00 : a 0 = 0 := ha.map_zero
    have : e₀ = 0 := a.injective (hz.trans h00.symm)
    have := congrFun this 0
    simp [he00] at this
  apply hσ
  refine RingEquiv.ext fun t => ?_
  have h2 := (h1 t).1
  rw [hμ] at h2
  have := mul_right_cancel₀ hμ0 h2
  simpa using this

theorem not_commute_rootGrp {σ : F ≃+* F} (hσ : σ ≠ 1) {a : Equiv.Perm (Fin 2 → F)}
    (ha : IsSemilinearWith a σ) (hadd : ∀ x y, a (x + y) = a x + a y)
    (p : ℙ F (Fin 2 → F))
    (hcomm : ∀ g ∈ rootGrp p, slPerm F g * a = a * slPerm F g) : False := by
  obtain ⟨x₀, hx₀⟩ := exists_smul_pt0 p
  set s : Equiv.Perm (Fin 2 → F) := slPerm F x₀ with hs
  have hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      IsSemilinearWith (slPerm F A) (1 : F ≃+* F) :=
    fun A => by rw [slPerm_eq_semilinPerm]; exact semilinPerm_isSemilinear A 1
  have hsadd : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (x y : Fin 2 → F),
      slPerm F A (x + y) = slPerm F A x + slPerm F A y := fun A x y => by
    rw [slPerm_eq_semilinPerm]; exact semilinPerm_add A 1 x y
  have ha' : IsSemilinearWith (s⁻¹ * a * s) σ := by
    have h1 : IsSemilinearWith (s⁻¹) (1 : F ≃+* F) := by
      have := hsl x₀⁻¹
      rwa [map_inv] at this
    have := (h1.mul ha).mul (hsl x₀)
    simpa using this
  have hadd' : ∀ x y, (s⁻¹ * a * s) (x + y) = (s⁻¹ * a * s) x + (s⁻¹ * a * s) y := by
    intro x y
    show s⁻¹ (a (s (x + y))) = s⁻¹ (a (s x)) + s⁻¹ (a (s y))
    have h1 : s (x + y) = s x + s y := hsadd x₀ x y
    have h2 : s⁻¹ = slPerm F x₀⁻¹ := (map_inv _ _).symm
    rw [h1, hadd, h2, hsadd]
  refine not_commute_unipotent hσ ha' hadd' fun t => ?_
  have hmem : x₀ * CFSG.SL2MinimalFaithful.unipotent t * x₀⁻¹ ∈ rootGrp p := by
    rw [← hx₀, mem_rootGrp_smul_iff]
    have : x₀⁻¹ * (x₀ * CFSG.SL2MinimalFaithful.unipotent t * x₀⁻¹) * x₀ =
        CFSG.SL2MinimalFaithful.unipotent t := by group
    rw [this, rootGrp_pt0]
    exact ⟨Multiplicative.ofAdd t, rfl⟩
  have h := hcomm _ hmem
  simp only [map_mul, map_inv] at h
  set u := slPerm F (CFSG.SL2MinimalFaithful.unipotent t)
  calc u * (s⁻¹ * a * s) = s⁻¹ * (s * u * s⁻¹ * a) * s := by group
    _ = s⁻¹ * (a * (s * u * s⁻¹)) * s := by rw [h]
    _ = (s⁻¹ * a * s) * u := by group

theorem exists_rootGrp_le_of_isPGroup [Finite F] {f : ℕ} (hf : Nat.card F = 2 ^ f)
    {X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hXp : IsPGroup 2 X) :
    ∃ p : ℙ F (Fin 2 → F), X ≤ rootGrp p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hf1 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hf
    omega
  have hP : Nat.card P.toSubgroup = Nat.card F := by
    rw [P.card_eq_multiplicity, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hf]
    have h1 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 hf1) two_ne_zero
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h4 : 4 ≤ (2 ^ f) ^ 2 := by
      have : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hf1)
      nlinarith
    have hodd : ¬ 2 ∣ (2 ^ f) ^ 2 - 1 := by omega
    have hne : (2 ^ f) ^ 2 - 1 ≠ 0 := by omega
    rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  obtain ⟨p, hp⟩ := exists_point_eq_rootGrp Nat.prime_two hf (P := P.toSubgroup) hP
  exact ⟨p, hXP.trans hp.le⟩

theorem card_fixed_le_matrix {K : Type*} [Field K] [Finite K] {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ≠ 1) : Nat.card {u : Fin 2 → K // g.mulVec u = u} ≤ Nat.card K := by
  classical
  let F : Submodule K (Fin 2 → K) := LinearMap.ker (Matrix.toLin' (g - 1))
  have hF : F ≠ ⊤ := by
    intro h
    apply hg
    have h0 : Matrix.toLin' (g - 1) = 0 := LinearMap.ker_eq_top.mp h
    have : g - 1 = 0 := Matrix.toLin'.injective (by rw [h0, map_zero])
    exact sub_eq_zero.mp this
  have hlt : Module.finrank K F < 2 := by
    have := Submodule.finrank_lt hF
    simpa using this
  have hcardF : Nat.card F = Nat.card K ^ Module.finrank K F := Module.natCard_eq_pow_finrank
  have e : {u : Fin 2 → K // g.mulVec u = u} ≃ F :=
    { toFun := fun u => ⟨u.1, by
        show Matrix.toLin' (g - 1) u.1 = 0
        rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, u.2, sub_self]⟩
      invFun := fun u => ⟨u.1, by
        have h : Matrix.toLin' (g - 1) u.1 = 0 := u.2
        rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
        exact h⟩
      left_inv := fun u => rfl
      right_inv := fun u => rfl }
  rw [Nat.card_congr e, hcardF]
  calc Nat.card K ^ Module.finrank K F ≤ Nat.card K ^ 1 :=
        Nat.pow_le_pow_right Nat.card_pos (by omega)
    _ = Nat.card K := pow_one _

end SL2

variable {G : Type} [Group G] [Finite G]

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem relIndex_le_card_aut {S : Subgroup G} (hSM : S ≤ M) (hS : IsPGroup 2 S) :
    (S ⊓ (L ⊔ QM L M)).relIndex S ≤ n := by
  let f : ↥S →* (Fq n ≃+* Fq n) := H.chi.comp (Subgroup.inclusion hSM)
  have hker : f.ker = (S ⊓ (L ⊔ QM L M)).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      obtain ⟨k, hk⟩ := hS x
      have hx2 : (Subgroup.inclusion hSM x) ^ 2 ^ k = 1 := Subtype.ext (by
        have := congrArg (fun z : ↥S => (z : G)) hk
        simpa using this)
      exact H.mem_LQ_of_chi_eq_one hx2 hx
    · intro hx
      exact H.chi_of_mem_LQ hx.2
  have h1 : (S ⊓ (L ⊔ QM L M)).relIndex S = f.ker.index := by
    rw [hker]
    rfl
  rw [h1, Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans
    (card_ringEquiv_le n H.n_ne_zero)

include H in
theorem card_fixed_actHom_of_sq {b : ↥M} (hb : H.actHom b * H.actHom b = 1)
    (hχ : H.chi b ≠ 1) :
    Nat.card {w : Fin 2 → Fq n // H.actHom b w = w} = Nat.card (Fq n) := by
  have hχχ : H.chi b * H.chi b = 1 := by
    have h1 := (H.isSemilinear_chi b).mul (H.isSemilinear_chi b)
    rw [hb] at h1
    exact IsSemilinearWith.unique (W := Fin 2 → Fq n) h1 IsSemilinearWith.one_perm
  have hinv : ∀ y : Fq n, H.chi b (H.chi b y) = y := fun y =>
    congrArg (fun s : Fq n ≃+* Fq n => s y) hχχ
  let β : (Fin 2 → Fq n) →+ (Fin 2 → Fq n) := AddMonoidHom.mk' (H.actHom b) (H.actHom_add b)
  have hβ : ∀ (c : Fq n) (w : Fin 2 → Fq n), β (c • w) = H.chi b c • β w :=
    fun c w => H.isSemilinear_chi b c w
  have hββ : ∀ w, β (β w) = w := fun w => by
    have := congrArg (fun p : Equiv.Perm (Fin 2 → Fq n) => p w) hb
    exact this
  have h := card_eq_sq_card_fixed (H.chi b) hχ hinv β hβ hββ
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at h
  exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h).symm

include H in
theorem card_fixed_le_card {s : G} (hsM : s ∈ M) {k : ℕ} (hk : s ^ 2 ^ k = 1)
    (hsQ : s ∉ QM L M) :
    Nat.card {w : Fin 2 → Fq n // H.actHom ⟨s, hsM⟩ w = w} ≤ Nat.card (Fq n) := by
  classical
  set x : ↥M := ⟨s, hsM⟩ with hx
  set a : Equiv.Perm (Fin 2 → Fq n) := H.actHom x with ha
  have ha1 : a ≠ 1 := fun h => hsQ ⟨hsM, (H.actHom_eq_one_iff x).1 h⟩
  have hxk : x ^ 2 ^ k = 1 := Subtype.ext (by simpa [hx] using hk)
  have hak : a ^ 2 ^ k = 1 := by rw [ha, ← map_pow, hxk, map_one]
  have hex : ∃ j, a ^ 2 ^ j = 1 := ⟨k, hak⟩
  set j := Nat.find hex with hj
  have hj1 : a ^ 2 ^ j = 1 := Nat.find_spec hex
  have hjpos : j ≠ 0 := fun h0 => ha1 (by simpa [h0] using hj1)
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hnot : a ^ 2 ^ i ≠ 1 := Nat.find_min hex (by omega)
  set y : ↥M := x ^ 2 ^ i with hy
  have hay : H.actHom y = a ^ 2 ^ i := by rw [hy, map_pow]
  have hay2 : H.actHom y * H.actHom y = 1 := by
    rw [hay, ← pow_two, ← pow_mul, ← pow_succ, ← hi]
    exact hj1
  have hsub : ∀ w, a w = w → H.actHom y w = w := by
    intro w hw
    rw [hay]
    have : ∀ m : ℕ, (a ^ m) w = w := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, Equiv.Perm.mul_apply, hw, ih]
    exact this _
  refine (Nat.card_le_card_of_injective (fun w : {w : Fin 2 → Fq n // a w = w} =>
    (⟨w.1, hsub w.1 w.2⟩ : {w : Fin 2 → Fq n // H.actHom y w = w})) (fun u v h => Subtype.ext
      (congrArg (fun z : {w : Fin 2 → Fq n // H.actHom y w = w} => z.1) h))).trans ?_
  by_cases hχ : H.chi y = 1
  · have hy2k : y ^ 2 ^ k = 1 := by
      rw [hy, ← pow_mul, mul_comm, pow_mul, hxk, one_pow]
    have hyLQ : (y : G) ∈ L ⊔ QM L M := H.mem_LQ_of_chi_eq_one hy2k hχ
    set g := H.rho ⟨y, hyLQ⟩ with hg
    have hyg : H.actHom y = slPerm (Fq n) g := (H.slPerm_rho ⟨y, hyLQ⟩).symm
    have hg1 : (g : Matrix (Fin 2) (Fin 2) (Fq n)) ≠ 1 := by
      intro h
      apply hnot
      rw [← hay, hyg]
      have : g = 1 := Subtype.ext h
      rw [this, map_one]
    refine le_trans (le_of_eq ?_) (card_fixed_le_matrix hg1)
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    rw [hyg, slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
    exact Iff.rfl
  · exact le_of_eq (H.card_fixed_actHom_of_sq hay2 hχ)

include H in
theorem exists_root_point_of_isPGroup (X : Subgroup G) (hX : X ≤ L ⊔ QM L M)
    (hX2 : IsPGroup 2 X) : ∃ p : ℙ (Fq n) (Fin 2 → Fq n), (H.rhoOn X hX).range ≤ rootGrp p := by
  have hn : n ≠ 0 := H.n_ne_zero
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_rootGrp_le_of_isPGroup (f := n) (GaloisField.card 2 n hn) ?_
  exact hX2.of_surjective (H.rhoOn X hX).rangeRestrict (MonoidHom.rangeRestrict_surjective _)

include H in
theorem exists_actHom_conj_ne (N : Subgroup G) (hN : N ≤ L ⊔ QM L M) {b : G} (hbM : b ∈ M)
    (hbχ : H.chi ⟨b, hbM⟩ ≠ 1) (p : ℙ (Fq n) (Fin 2 → Fq n))
    (hfull : ∀ g ∈ rootGrp p, ∃ x : ↥N, H.rhoOn N hN x = g) :
    ∃ (x : G) (hx : x ∈ N), H.actHom (⟨b, hbM⟩ * ⟨x, H.LQ_le (hN hx)⟩ * ⟨b, hbM⟩⁻¹) ≠
      H.actHom ⟨x, H.LQ_le (hN hx)⟩ := by
  by_contra hcon
  push Not at hcon
  refine not_commute_rootGrp (σ := H.chi ⟨b, hbM⟩) hbχ (H.isSemilinear_chi ⟨b, hbM⟩)
    (H.actHom_add ⟨b, hbM⟩) p fun g hg => ?_
  obtain ⟨x, hx⟩ := hfull g hg
  have h1 : slPerm (Fq n) g = H.actHom ⟨x, H.LQ_le (hN x.2)⟩ := by
    rw [← hx, rhoOn_apply, H.slPerm_rho]
  have h2 := hcon x x.2
  rw [map_mul, map_mul, map_inv] at h2
  rw [h1]
  set a := H.actHom ⟨b, hbM⟩
  set α := H.actHom ⟨x, H.LQ_le (hN x.2)⟩
  calc α * a = (a * α * a⁻¹) * a := by rw [h2]
    _ = a * α := by group

end MData

end CFSG.CGT.PushingUpLit.T2KR

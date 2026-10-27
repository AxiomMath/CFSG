module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace GL83.I243

open CFSG.Open

theorem exists_conj_image {X : Type*} [Group X] {p : ℕ} {K B : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hBel : IsElemAbelian p B) :
    ∃ Im : Subgroup (MulAut ↥K), IsElemAbelian p Im ∧
      (∀ ε ∈ Im, ∃ f ∈ B, ∀ y : ↥K, ((ε y : ↥K) : X) = f * (y : X) * f⁻¹) ∧
      (∀ f ∈ B, ∃ ε ∈ Im, ∀ y : ↥K, ((ε y : ↥K) : X) = f * (y : X) * f⁻¹) ∧
      Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) * Nat.card Im =
        Nat.card B := by
  let φ : B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hφ : ∀ (b : B) (y : ↥K), ((φ b y : ↥K) : X) = (b : X) * (y : X) * (b : X)⁻¹ :=
    fun b y => rfl
  have hIm : IsElemAbelian p φ.range := by
    have h := (hBel.subgroupOf B).map φ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
  have hker : φ.ker = (B ⊓ Subgroup.centralizer (K : Set X)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨b.2, fun y hy => ?_⟩
      have h1 := congrArg (fun a : ↥K => (a : X)) (DFunLike.congr_fun h ⟨y, hy⟩)
      simp only [hφ, MulAut.one_apply] at h1
      calc y * (b : X) = ((b : X) * y * (b : X)⁻¹) * (b : X) := by rw [h1]
        _ = (b : X) * y := by group
    · rintro ⟨-, h⟩
      ext y
      rw [hφ, MulAut.one_apply, mul_inv_eq_iff_eq_mul, ← h y y.2]
  refine ⟨φ.range, hIm, ?_, ?_, ?_⟩
  · rintro ε ⟨b, rfl⟩
    exact ⟨(b : X), b.2, hφ b⟩
  · intro f hf
    exact ⟨φ ⟨f, hf⟩, ⟨⟨f, hf⟩, rfl⟩, hφ ⟨f, hf⟩⟩
  · have h := Subgroup.card_ker_mul_card_range φ
    rwa [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h

theorem exists_elemAbelian_image
    {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hBel : IsElemAbelian p B)
    {z : X} (hzB : z ∈ B) (hzp : orderOf z = p)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z)
    {n : ℕ} (hB : p ^ (n + 1) ≤ Nat.card B) :
    ∃ E : Subgroup (MulAut ↥K), IsElemAbelian p E ∧ Nat.card E = p ^ n ∧
      ∀ ε ∈ E, ∃ f ∈ B, ∀ y : ↥K, ((ε y : ↥K) : X) = f * (y : X) * f⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Im, hIm, hIm1, -, hcard⟩ := exists_conj_image hBN hBel
  have hC : Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) ≤ p := by
    have hle : B ⊓ Subgroup.centralizer (K : Set X) ≤ Subgroup.zpowers z :=
      fun b hb => hCB b hb.1 hb.2
    calc Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X)
        ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hle
      _ = p := by rw [Nat.card_zpowers, hzp]
  have hImn : p ^ n ≤ Nat.card Im := by
    have h1 : p * p ^ n ≤ p * Nat.card Im :=
      calc p * p ^ n = p ^ (n + 1) := (pow_succ' p n).symm
        _ ≤ Nat.card B := hB
        _ = Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) * Nat.card Im :=
          hcard.symm
        _ ≤ p * Nat.card Im := Nat.mul_le_mul_right _ hC
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  obtain ⟨m, hm⟩ := hBel.isPGroup.exists_card_eq
  have hdvd : Nat.card Im ∣ p ^ m := by
    rw [← hm, ← hcard]
    exact Dvd.intro_left _ rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hjn : n ≤ j := by
    rw [hj] at hImn
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hImn
  haveI : Finite Im := Nat.finite_of_card_ne_zero (by rw [hj]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨E, hEcard, -, hEIm⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
    (n := n) (H := ⊥) (L := Im) (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hj]; exact pow_dvd_pow p hjn) bot_le
  exact ⟨E, hIm.mono hEIm, hEcard, fun ε hε => hIm1 ε (hEIm hε)⟩

theorem exists_plane_image
    {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hBel : IsElemAbelian p B)
    {z : X} (hzB : z ∈ B) (hzp : orderOf z = p)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z)
    (hB3 : p ^ 3 ≤ Nat.card B) :
    ∃ E : Subgroup (MulAut ↥K), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ ε ∈ E, ∃ f ∈ B, ∀ y : ↥K, ((ε y : ↥K) : X) = f * (y : X) * f⁻¹ :=
  exists_elemAbelian_image hp hBN hBel hzB hzp hCB (n := 2) hB3

theorem exists_plane_image_eq
    {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hBel : IsElemAbelian p B)
    {z : X} (hzB : z ∈ B) (hzp : orderOf z = p)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z)
    (hB3 : Nat.card B = p ^ 3) (hzC : z ∈ Subgroup.centralizer (K : Set X)) :
    ∃ E : Subgroup (MulAut ↥K), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      (∀ ε ∈ E, ∃ f ∈ B, ∀ y : ↥K, ((ε y : ↥K) : X) = f * (y : X) * f⁻¹) ∧
      (∀ f ∈ B, ∃ ε ∈ E, ∀ y : ↥K, ((ε y : ↥K) : X) = f * (y : X) * f⁻¹) := by
  obtain ⟨Im, hIm, hIm1, hIm2, hcard⟩ := exists_conj_image hBN hBel
  have hker : B ⊓ Subgroup.centralizer (K : Set X) = Subgroup.zpowers z :=
    le_antisymm (fun b hb => hCB b hb.1 hb.2)
      (fun b hb => ⟨Subgroup.zpowers_le.mpr hzB hb, Subgroup.zpowers_le.mpr hzC hb⟩)
  rw [hker, Nat.card_zpowers, hzp, hB3, pow_succ'] at hcard
  exact ⟨Im, hIm, Nat.eq_of_mul_eq_mul_left hp.pos hcard, hIm1, hIm2⟩

end GL83.I243

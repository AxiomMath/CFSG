module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.Semidihedral.AllPrime

namespace SL2Sections

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.Glauberman.Dickson
open scoped commutatorElement

universe u v

theorem neg_one_ne_one_of_odd_card {F : Type u} [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    (-1 : F) ≠ 1 := by
  intro h
  have : Fintype F := Fintype.ofFinite F
  have hq := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card] at hq
  obtain ⟨k, hk⟩ := hF
  rw [hk] at hq
  push_cast at hq
  have h2 : (2 : F) = 0 := by
    rw [← one_add_one_eq_two]
    nth_rewrite 1 [← h]
    exact neg_add_cancel 1
  rw [h2, zero_mul, zero_add] at hq
  exact one_ne_zero hq

private theorem mul_sq_sub_one_lt {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) :
    x * (x ^ 2 - 1) < y * (y ^ 2 - 1) := by
  have hy : 2 ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h1 : x * (x ^ 2 - 1) ≤ x * (y ^ 2 - 1) :=
    Nat.mul_le_mul_left x (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy.le 2) 1)
  have h2 : x * (y ^ 2 - 1) < y * (y ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hxy (by omega)
  exact h1.trans_lt h2

private theorem eq_of_mul_sq_sub_one_eq {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : x * (x ^ 2 - 1) = y * (y ^ 2 - 1)) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (mul_sq_sub_one_lt hx hlt).ne
  · exact heq
  · exact absurd h (mul_sq_sub_one_lt hy hgt).ne'

private theorem odd_sq_mod_four {x : ℕ} (hx : Odd x) : x ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hx
  ring_nf
  omega

private theorem torus_aux {q w z : ℕ}
    (hw : (q % 4 = 1 ∧ 2 * w = q + 1) ∨ (q % 4 = 3 ∧ 2 * w = q - 1)) (hw3 : 3 ≤ w)
    (hwz : w ∣ z) (h2z : 2 ∣ z) (hz : z ∣ (q - 1) / 2 ∨ z ∣ (q + 1) / 2) : False := by
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hodd : w % 2 = 1 := by omega
    have ha : (q - 1) / 2 = w - 1 := by omega
    have hb : (q + 1) / 2 = w := by omega
    rcases hz with hz | hz
    · rw [ha] at hz
      have := Nat.le_of_dvd (by omega) (hwz.trans hz)
      omega
    · rw [hb] at hz
      have := h2z.trans hz
      omega
  · have hodd : w % 2 = 1 := by omega
    have ha : (q - 1) / 2 = w := by omega
    have hb : (q + 1) / 2 = w + 1 := by omega
    rcases hz with hz | hz
    · rw [ha] at hz
      have := h2z.trans hz
      omega
    · rw [hb] at hz
      have h1 : w ∣ 1 := (Nat.dvd_add_right (dvd_refl w)).mp (hwz.trans hz)
      have := Nat.le_of_dvd one_pos h1
      omega

private theorem subfield_aux {p f m w : ℕ} (hp : p.Prime) (hpodd : Odd p) (hm : m ≠ 0)
    (hmf : 2 * m ≤ f)
    (hw : (p ^ f % 4 = 1 ∧ 2 * w = p ^ f + 1) ∨ (p ^ f % 4 = 3 ∧ 2 * w = p ^ f - 1))
    (hdvd : w ∣ p ^ m * ((p ^ m) ^ 2 - 1)) : False := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := hpodd
    omega
  have hpm : 3 ≤ p ^ m := (Nat.le_self_pow hm p).trans' hp3
  have hf : 1 ≤ f := by omega
  have hcop : Nat.Coprime w (p ^ m) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hpw
    have hpf : p ∣ p ^ f := dvd_pow_self p (by omega)
    have h2w : p ∣ 2 * w := hpw.mul_left 2
    rcases hw with ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [h2] at h2w
      have := (Nat.dvd_add_right hpf).mp h2w
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · rw [h2] at h2w
      have hsub : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpf h2w
      have hpos : 0 < p ^ f := pow_pos hp.pos f
      rw [show p ^ f - (p ^ f - 1) = 1 by omega] at hsub
      exact hp.one_lt.ne' (Nat.dvd_one.mp hsub)
  have hdvd' : w ∣ (p ^ m) ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hdvd
  have hsq : 9 ≤ (p ^ m) ^ 2 := by nlinarith
  have hoddpm : Odd (p ^ m) := hpodd.pow
  have hsqmod := odd_sq_mod_four hoddpm
  have hwodd : w % 2 = 1 := by rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hhalf : w ∣ ((p ^ m) ^ 2 - 1) / 2 := by
    have h2 : (p ^ m) ^ 2 - 1 = 2 * (((p ^ m) ^ 2 - 1) / 2) := by omega
    rw [h2] at hdvd'
    have hc2 : Nat.Coprime w 2 := by
      rw [Nat.coprime_two_right]
      exact Nat.odd_iff.mpr hwodd
    exact hc2.dvd_of_dvd_mul_left hdvd'
  have hle : w ≤ ((p ^ m) ^ 2 - 1) / 2 := Nat.le_of_dvd (by omega) hhalf
  have hqle : (p ^ m) ^ 2 ≤ p ^ f := by
    rw [← pow_mul, mul_comm]
    exact Nat.pow_le_pow_right hp.pos hmf
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · have heq : p ^ f = (p ^ m) ^ 2 := by omega
    rw [heq] at h1
    omega

theorem card_psl2_mul_two {F : Type u} [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    Nat.card (PSL2MatrixGroup F) * 2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have h := huppert614_card_psl_mul_center (K := F)
  rwa [huppert614_card_center_of_neg_one_ne_one (neg_one_ne_one_of_odd_card hF)] at h

theorem not_isPerfect_pgl2
    {F : Type u} [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    ¬ Group.IsPerfect (Matrix.ProjGenLinGroup (Fin 2) F) := by
  intro hperf
  have hidx := h826_pslToPGL_range_index_eq_two (K := F) (neg_one_ne_one_of_odd_card hF)
  set R := (h826_pslToPGL (K := F)).range with hR
  have : R.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (Matrix.ProjGenLinGroup (Fin 2) F ⧸ R) = 2 := hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (Matrix.ProjGenLinGroup (Fin 2) F ⧸ R) := isCyclic_of_prime_card hcard
  let : CommGroup (Matrix.ProjGenLinGroup (Fin 2) F ⧸ R) := IsCyclic.commGroup
  have hle : commutator (Matrix.ProjGenLinGroup (Fin 2) F) ≤ R := by
    simpa only [QuotientGroup.ker_mk'] using
      Abelianization.commutator_subset_ker (QuotientGroup.mk' R)
  rw [@Group.IsPerfect.commutator_eq_top _ _ hperf, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hidx
  omega

private theorem not_isPerfect_of_surjective_comm {X A : Type*} [Group X] [CommGroup A]
    [Nontrivial A] (φ : X →* A) (hφ : Function.Surjective φ) : ¬ Group.IsPerfect X := by
  intro hperf
  have hle := Abelianization.commutator_subset_ker φ
  rw [@Group.IsPerfect.commutator_eq_top _ _ hperf, top_le_iff] at hle
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨x, rfl⟩ := hφ a
  exact ha ((MonoidHom.mem_ker).mp (hle ▸ Subgroup.mem_top x))

private theorem card_eq_one_of_isPerfect_comm {X : Type*} [Group X] (hperf : Group.IsPerfect X)
    (hcomm : ∀ a b : X, a * b = b * a) : Nat.card X = 1 := by
  have hle : commutator X ≤ ⊥ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, hcomm a b, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  rw [@Group.IsPerfect.commutator_eq_top _ _ hperf, le_bot_iff] at hle
  rw [← Subgroup.card_top (G := X), hle, Subgroup.card_bot]

private def dihedralParity (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun
    | .r _ => 1
    | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (a | a) (b | b) <;> simp only [DihedralGroup.r_mul_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    · rfl
    · exact (one_mul _).symm
    · exact (mul_one _).symm
    · change Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd (1 + 1)
      decide

private theorem dihedral_not_isPerfect (n : ℕ) : ¬ Group.IsPerfect (DihedralGroup n) := by
  have : Nontrivial (Multiplicative (ZMod 2)) := by
    refine ⟨⟨1, Multiplicative.ofAdd 1, ?_⟩⟩
    decide
  refine not_isPerfect_of_surjective_comm (dihedralParity n) ?_
  intro a
  have ha : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
    revert a
    decide
  rcases ha with rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨DihedralGroup.sr 0, rfl⟩

private theorem card_alternating_four : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem card_alternating_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

private theorem alternating_five_pow_fifteen : ∀ g : alternatingGroup (Fin 5),
    g ^ 15 = 1 → g ^ 5 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel

private theorem card_psl2_galoisField {p m : ℕ} [Fact p.Prime] (hpodd : Odd p) (hm : m ≠ 0) :
    Nat.card (PSL2MatrixGroup (GaloisField p m)) * 2 = p ^ m * ((p ^ m) ^ 2 - 1) := by
  have hcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
  have h := card_psl2_mul_two (F := GaloisField p m) (by rw [hcard]; exact hpodd.pow)
  rwa [hcard] at h

private theorem card_sup_of_disjoint {X : Type*} [Group X] [Finite X] (N C : Subgroup X)
    [N.Normal] (hdis : Disjoint N C) (htop : N ⊔ C = ⊤) :
    Nat.card X = Nat.card N * Nat.card C := by
  have h1 := Subgroup.relIndex_sup_right C N
  rw [sup_comm, htop, Subgroup.relIndex_top_right] at h1
  have h2 : N.relIndex C = Nat.card C := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr hdis, Subgroup.index_bot]
  rw [← Subgroup.card_mul_index N, h1, h2]

theorem psl2_perfect_subgroup_onto_psl2
    {F : Type u} [Field F] [Finite F] {F' : Type v}
    [Field F'] [Finite F'] {p f : ℕ} [Fact p.Prime] (hpodd : Odd p) (hF : Nat.card F = p ^ f)
    (hF' : 7 ≤ Nat.card F') (hF'odd : Odd (Nat.card F'))
    (X : Subgroup (PSL2MatrixGroup F)) (hX : Group.IsPerfect X)
    (π : X →* PSL2MatrixGroup F') (hπ : Function.Surjective π) :
    ∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧ Nat.card F' = p ^ m := by
  have hcard' := card_psl2_mul_two hF'odd
  have hbig : 168 ≤ Nat.card (PSL2MatrixGroup F') := by
    have h1 : 7 * (7 ^ 2 - 1) ≤ Nat.card F' * (Nat.card F' ^ 2 - 1) :=
      Nat.mul_le_mul hF' (Nat.sub_le_sub_right (Nat.pow_le_pow_left hF' 2) 1)
    omega
  have hXbig : 168 ≤ Nat.card X := hbig.trans (Nat.card_le_card_of_surjective π hπ)
  have hX1 : Nat.card X ≠ 1 := by omega
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hF X with
    hE | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNe, -, hC, -, -, hNC⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, ⟨e⟩⟩
  · exact absurd (card_eq_one_of_isPerfect_comm hX
      (fun a b => (hE.toIsMulCommutative.is_comm.comm a b))) hX1
  · let : CommGroup X := IsCyclic.commGroup
    exact absurd (card_eq_one_of_isPerfect_comm hX (fun a b => mul_comm a b)) hX1
  · exact absurd (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
      (dihedral_not_isPerfect z)
  · rw [Nat.card_congr e.toEquiv, card_alternating_four] at hXbig
    omega
  · rw [Nat.card_congr e.toEquiv, card_perm_four] at hXbig
    omega
  · rw [Nat.card_congr e.toEquiv, card_alternating_five] at hXbig
    omega
  ·
    exfalso
    have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hNe.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
      intro a ha b hb
      let : CommGroup C := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : C) ⟨b, hb⟩)
    have hcomm : commutator X ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
        (hNC ▸ Subgroup.mem_top a)
      obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
        (hNC ▸ Subgroup.mem_top b)
      have h1 : QuotientGroup.mk' N n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
      have h2 : QuotientGroup.mk' N n₂ = 1 := (QuotientGroup.eq_one_iff n₂).mpr hn₂
      have hq : QuotientGroup.mk' N ⁅n₁ * c₁, n₂ * c₂⁆ = 1 := by
        rw [map_commutatorElement, map_mul, map_mul, h1, h2,
          one_mul, one_mul, ← map_commutatorElement, commutatorElement_def,
          hCcomm c₁ hc₁ c₂ hc₂, mul_inv_cancel_right, mul_inv_cancel, map_one]
      exact (QuotientGroup.eq_one_iff _).mp hq
    rw [@Group.IsPerfect.commutator_eq_top _ _ hX, top_le_iff] at hcomm
    exact hX1 (card_eq_one_of_isPerfect_comm hX fun a b =>
      hNcomm a (hcomm ▸ Subgroup.mem_top a) b (hcomm ▸ Subgroup.mem_top b))
  ·
    have hgal := card_psl2_galoisField (p := p) hpodd hm
    have hXcard : Nat.card X = Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
      Nat.card_congr e.toEquiv
    have hgcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      obtain ⟨k, hk⟩ := hpodd
      omega
    have hpm : 3 ≤ p ^ m := (Nat.le_self_pow hm p).trans' hp3
    have hpm3 : p ^ m ≠ 3 := by
      intro h3
      rw [h3] at hgal
      omega
    have hpm2 : p ^ m ≠ 2 := by omega
    have : IsSimpleGroup (PSL2MatrixGroup (GaloisField p m)) :=
      huppert_II_6_13 2 le_rfl (Or.inr (by rw [hgcard]; exact hpm2))
        (Or.inr (by rw [hgcard]; exact hpm3))
    have : IsSimpleGroup X := e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hker | hker
    · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
      have hbij := Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)
      refine ⟨m, hm, hmf, ?_⟩
      have heq : p ^ m * ((p ^ m) ^ 2 - 1) = Nat.card F' * (Nat.card F' ^ 2 - 1) := by
        rw [← hgal, ← hcard', ← hXcard, hbij]
      exact (eq_of_mul_sq_sub_one_eq (by omega) (by omega) heq).symm
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : PSL2MatrixGroup F')
      · obtain ⟨x, rfl⟩ := hπ y
        exact hy ((MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top x))
  ·
    exfalso
    have hgcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    exact not_isPerfect_pgl2 (F := GaloisField p m) (by rw [hgcard]; exact hpodd.pow)
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

theorem psl2_subgroup_eq_top_or_small
    {F : Type u} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hpodd : Odd p) (hF : Nat.card F = p ^ f) (hq : 5 < p ^ f) {w : ℕ}
    (hw : (p ^ f % 4 = 1 ∧ 2 * w = p ^ f + 1) ∨ (p ^ f % 4 = 3 ∧ 2 * w = p ^ f - 1))
    (X : Subgroup (PSL2MatrixGroup F)) (h4 : 4 ∣ Nat.card X) (x : X) (hx : orderOf x = w) :
    X = ⊤ ∨ (w = 3 ∧ (Nonempty (X ≃* alternatingGroup (Fin 4)) ∨
        Nonempty (X ≃* Equiv.Perm (Fin 4)))) ∨
      (w = 5 ∧ Nonempty (X ≃* alternatingGroup (Fin 5))) := by
  have hp := (Fact.out : p.Prime)
  have hwX : w ∣ Nat.card X := hx ▸ orderOf_dvd_natCard x
  have hw3 : 3 ≤ w := by rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hwodd : w % 2 = 1 := by rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hcw2 : Nat.Coprime w 2 := by
    rw [Nat.coprime_two_right]
    exact Nat.odd_iff.mpr hwodd
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    rw [hF]
    obtain ⟨k, hk⟩ := hqodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_right (dvd_mul_right 2 k)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hq
      omega
    · exact h
  have hcwp : ∀ k : ℕ, Nat.Coprime w (p ^ k) := by
    intro k
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hpw
    have hpf : p ∣ p ^ f := dvd_pow_self p (by omega)
    have h2w : p ∣ 2 * w := hpw.mul_left 2
    rcases hw with ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [h2] at h2w
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpf).mp h2w))
    · rw [h2] at h2w
      have hsub : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpf h2w
      rw [show p ^ f - (p ^ f - 1) = 1 by omega] at hsub
      exact hp.one_lt.ne' (Nat.dvd_one.mp hsub)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hF X with
    hE | ⟨z, hz, hzX, -⟩ | ⟨z, hz, hzX, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h5, ⟨e⟩⟩ |
      ⟨m, t, -, ht, N, C, hN, -, hNm, -, hCt, hdis, hNC⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ |
      ⟨m, hm, hmf, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p X).exists_card_eq
    rw [hk] at h4
    have h2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow ((dvd_trans ⟨2, rfl⟩ h4))
    obtain ⟨j, hj⟩ := hpodd
    omega
  · exfalso
    rw [hgcd, hF] at hz
    rw [hzX] at hwX h4
    exact torus_aux hw hw3 hwX (dvd_trans ⟨2, rfl⟩ h4) hz
  · exfalso
    rw [hgcd, hF] at hz
    rw [hzX] at hwX h4
    exact torus_aux hw hw3 (hcw2.dvd_of_dvd_mul_left hwX)
      (by obtain ⟨k, hk⟩ := h4; exact ⟨k, by omega⟩) hz
  · rw [Nat.card_congr e.toEquiv, card_alternating_four] at hwX
    have hle := Nat.le_of_dvd (by norm_num) hwX
    have hw' : w = 3 := by interval_cases w <;> simp_all
    exact Or.inr (Or.inl ⟨hw', Or.inl ⟨e⟩⟩)
  · rw [Nat.card_congr e.toEquiv, card_perm_four] at hwX
    have hle := Nat.le_of_dvd (by norm_num) hwX
    have hw' : w = 3 := by interval_cases w <;> simp_all
    exact Or.inr (Or.inl ⟨hw', Or.inr ⟨e⟩⟩)
  · rw [Nat.card_congr e.toEquiv, card_alternating_five] at hwX
    have hle := Nat.le_of_dvd (by norm_num) hwX
    have hw' : w = 3 ∨ w = 5 ∨ w = 15 := by interval_cases w <;> simp_all
    rcases hw' with rfl | rfl | rfl
    ·
      exfalso
      have hq7 : p ^ f = 7 := by rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      rcases h5 with rfl | h5
      · have : 5 ∣ 5 ^ f := dvd_pow_self 5 (by omega)
        rw [hq7] at this
        omega
      · rw [show 2 * f = f * 2 by ring, pow_mul, hq7] at h5
        omega
    · exact Or.inr (Or.inr ⟨rfl, ⟨e⟩⟩)
    · exfalso
      have hx' : orderOf (e x) = 15 := by rw [MulEquiv.orderOf_eq, hx]
      rcases alternating_five_pow_fifteen (e x) (hx' ▸ pow_orderOf_eq_one (e x)) with h | h
      · have := orderOf_dvd_of_pow_eq_one h
        rw [hx'] at this
        omega
      · have := orderOf_dvd_of_pow_eq_one h
        rw [hx'] at this
        omega
  ·
    exfalso
    have hcard := card_sup_of_disjoint N C hdis hNC
    rw [hcard, hNm, hCt] at hwX h4
    have hc4 : Nat.Coprime 4 (p ^ m) := by
      apply Nat.Coprime.pow_right
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_two_left]
      exact hpodd
    have ht' : t ∣ (p ^ f - 1) / 2 := by
      have hg : Nat.gcd (p ^ f - 1) 2 = 2 := by rw [← hF]; exact hgcd
      rwa [hg] at ht
    exact torus_aux hw hw3 ((hcwp m).dvd_of_dvd_mul_left hwX)
      (dvd_trans ⟨2, rfl⟩ (hc4.dvd_of_dvd_mul_left h4)) (Or.inl ht')
  ·
    have hgal := card_psl2_galoisField (p := p) hpodd hm
    rw [Nat.card_congr e.toEquiv] at hwX
    by_cases hmf' : m = f
    · left
      subst hmf'
      rw [← Subgroup.card_eq_iff_eq_top]
      have h := card_psl2_mul_two (F := F) (by rw [hF]; exact hqodd)
      rw [hF, ← hgal, ← Nat.card_congr e.toEquiv] at h
      omega
    · exfalso
      obtain ⟨k, rfl⟩ := hmf
      have hk : 2 ≤ k := by
        rcases k with _ | _ | k
        · omega
        · exact absurd (mul_one m).symm hmf'
        · omega
      exact subfield_aux hp hpodd hm (by nlinarith) hw
        (dvd_trans (dvd_mul_right w 2) (hgal ▸ Nat.mul_dvd_mul_right hwX 2))
  ·
    exfalso
    have hgcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    rw [Nat.card_congr e.toEquiv, huppertXI13_card_pgl2, hgcard] at hwX
    obtain ⟨k, hk⟩ := hmf
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk
        omega
      · exact h
    exact subfield_aux hp hpodd hm (by nlinarith) hw hwX

private theorem sq_eq_one_of_mem_center_sl2 {F : Type u} [Field F]
    {x : Matrix.SpecialLinearGroup (Fin 2) F}
    (hx : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : x ^ 2 = 1 := by
  obtain ⟨c, hc, hcx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  rw [Fintype.card_fin] at hc
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hcx, ← map_pow, hc,
    map_one]

private theorem mem_center_of_sq_eq_one_sl2 {F : Type u} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx : x ^ 2 = 1) :
    x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have h2 : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hF
  have hinv : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hx]
  rcases OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 x hinv with rfl | rfl
  · exact Subgroup.one_mem _
  · exact OddFieldSL2.minusIdentity_mem_center F

theorem mem_center_sl2_iff {F : Type u} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    have h2 : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hF
    have hinv : x⁻¹ = x := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, sq_eq_one_of_mem_center_sl2 hx]
    exact OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 x hinv
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact OddFieldSL2.minusIdentity_mem_center F

theorem card_ker_mul_card_range {Y Z : Type*} [Group Y] [Group Z] [Finite Y]
    (φ : Y →* Z) : Nat.card φ.ker * Nat.card φ.range = Nat.card Y := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem sl2_section_char_power
    {F : Type u} [Field F] [Finite F] {F' : Type v} [Field F']
    [Finite F'] {p f : ℕ} [Fact p.Prime] (hpodd : Odd p) (hF : Nat.card F = p ^ f)
    (hF'7 : 7 ≤ Nat.card F') (hF'odd : Odd (Nat.card F'))
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (φ : Y →* Matrix.SpecialLinearGroup (Fin 2) F) (hφ : Odd (Nat.card φ.ker))
    (ψ : Y →* Matrix.SpecialLinearGroup (Fin 2) F') (hψ : Function.Surjective ψ) :
    (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧ Nat.card F' = p ^ m) ∧
      (Nat.card F' = p ^ f → Function.Surjective φ) := by
  have hkk : φ.ker ≤ ψ.ker := by
    have hbot := OddLinearNormals.normal_odd_specialLinear_eq_bot F' hF'odd (by omega)
      (φ.ker.map ψ) (Subgroup.Normal.map inferInstance ψ hψ)
      (hφ.of_dvd_nat (Subgroup.card_map_dvd _ _))
    intro y hy
    have h1 : ψ y ∈ φ.ker.map ψ := Subgroup.mem_map_of_mem ψ hy
    rw [hbot] at h1
    exact h1
  refine ⟨?_, ?_⟩
  · let πF := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
    let π' := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F'))
    let α : Y →* PSL2MatrixGroup F := πF.comp φ
    have hkα : α.ker ≤ (π'.comp ψ).ker := by
      intro y hy
      have hc : φ y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff _).mp hy
      have hy2 : y ^ 2 ∈ ψ.ker := hkk (by
        rw [MonoidHom.mem_ker, map_pow]
        exact sq_eq_one_of_mem_center_sl2 hc)
      rw [MonoidHom.mem_ker, map_pow] at hy2
      exact (QuotientGroup.eq_one_iff _).mpr (mem_center_of_sq_eq_one_sl2 hF'odd hy2)
    let θ : α.range →* PSL2MatrixGroup F' :=
      (QuotientGroup.lift α.ker (π'.comp ψ) hkα).comp
        (QuotientGroup.quotientKerEquivRange α).symm.toMonoidHom
    have hθ : Function.Surjective θ := by
      intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ z
      obtain ⟨y, rfl⟩ := hψ w
      refine ⟨QuotientGroup.quotientKerEquivRange α (QuotientGroup.mk' α.ker y), ?_⟩
      change QuotientGroup.lift α.ker (π'.comp ψ) hkα
        ((QuotientGroup.quotientKerEquivRange α).symm
          (QuotientGroup.quotientKerEquivRange α (QuotientGroup.mk' α.ker y))) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    have hperf : Group.IsPerfect α.range :=
      Group.IsPerfect.ofSurjective (f := α.rangeRestrict) α.rangeRestrict_surjective
    exact psl2_perfect_subgroup_onto_psl2 hpodd hF hF'7 hF'odd α.range hperf θ hθ
  · intro heq
    have h1 := card_ker_mul_card_range φ
    have h2 := card_ker_mul_card_range ψ
    rw [MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top,
      huppert614_card_specialLinearGroup, heq] at h2
    have hle : Nat.card φ.ker ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hkk
    have hrange : Nat.card φ.range = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
      apply le_antisymm (Subgroup.card_le_card_group _)
      rw [huppert614_card_specialLinearGroup, hF]
      have hpos : 0 < Nat.card φ.ker := Nat.card_pos
      have hle' : Nat.card φ.ker * (p ^ f * ((p ^ f) ^ 2 - 1)) ≤
          Nat.card φ.ker * Nat.card φ.range := by
        rw [h1, ← h2]
        exact Nat.mul_le_mul_right _ hle
      exact Nat.le_of_mul_le_mul_left hle' hpos
    exact MonoidHom.range_eq_top.mp ((Subgroup.card_eq_iff_eq_top _).mp hrange)

theorem exists_perfect_section {B M : Type*} [Group B] [Group M] [Finite B]
    (β : B →* M) (hβ : Odd (Nat.card β.ker)) (Q : Subgroup M) [Q.Normal]
    (hsolv : Group.IsSolvable (M ⧸ Q)) (R : Subgroup B) [R.Normal] (hR : Odd (Nat.card R))
    (X : Subgroup (B ⧸ R)) (hX : Group.IsPerfect X) :
    ∃ Y : Subgroup B, Group.IsPerfect Y ∧ (∀ y ∈ Y, β y ∈ Q) ∧
      (∀ y ∈ Y, QuotientGroup.mk' R y ∈ X) ∧
      (∀ x ∈ X, ∃ y ∈ Y, QuotientGroup.mk' R y = x) ∧
      Odd (Nat.card (R ⊓ Y : Subgroup B)) ∧ Odd (Nat.card (β.ker ⊓ Y : Subgroup B)) := by
  let T : Subgroup B := X.comap (QuotientGroup.mk' R)
  let ηT : T →* X := ((QuotientGroup.mk' R).comp T.subtype).codRestrict X fun x => x.2
  have hηT : Function.Surjective ηT := by
    rintro ⟨q, hq⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective R q
    exact ⟨⟨b, hq⟩, rfl⟩
  obtain ⟨⟨k, hk, -⟩, -, hPperf, -⟩ := CFSG.perfect_residual_characterization (G := T)
  have hPmap : (CFSG.perfectResidual T).map ηT = ⊤ := by
    rw [hk, map_derivedSeries_eq hηT, Group.IsPerfect.derivedSeries_eq_top]
  let Y : Subgroup B := (CFSG.perfectResidual T).map T.subtype
  have hYT : Y ≤ T := Subgroup.map_subtype_le _
  have hYperf : Group.IsPerfect Y := Group.IsPerfect.map T.subtype
  refine ⟨Y, hYperf, ?_, fun y hy => hYT hy, ?_, ?_, ?_⟩
  ·
    have := hsolv
    let g : B →* M ⧸ Q := (QuotientGroup.mk' Q).comp β
    have hXperf : Group.IsPerfect (Y.map g) := Group.IsPerfect.map g
    have hXbot : Y.map g = ⊥ := by
      by_contra hne
      have : Nontrivial (Y.map g) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      have : Group.IsSolvable (Y.map g) := inferInstance
      exact Group.IsPerfect.not_isSolvable (Y.map g) inferInstance
    intro y hy
    have h1 : g y ∈ Y.map g := Subgroup.mem_map_of_mem g hy
    rw [hXbot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  · intro x hx
    have hx' : (⟨x, hx⟩ : X) ∈ (CFSG.perfectResidual T).map ηT := by
      rw [hPmap]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, hwx⟩ := hx'
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwx⟩
  · exact hR.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  · exact hβ.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

private theorem perm_five_eq_one_of_conj :
    ∀ (π : Equiv.Perm (Fin 5)) (c : alternatingGroup (Fin 5)), π * π = 1 → c ^ 5 = 1 →
      c ≠ 1 → π * (c : Equiv.Perm (Fin 5)) = c * π → π = 1 := by
  decide +kernel

private theorem perm_four_eq_one_of_conj :
    ∀ (π : Equiv.Perm (Fin 4)) (c : alternatingGroup (Fin 4)), π * π = 1 → c ^ 3 = 1 →
      c ≠ 1 → π * (c : Equiv.Perm (Fin 4)) = c * π → π = 1 := by
  decide +kernel

private theorem perm_four_sign_of_pow_three : ∀ g : Equiv.Perm (Fin 4),
    g ^ 3 = 1 → Equiv.Perm.sign g = 1 := by
  decide +kernel

theorem mulAut_eq_one_of_alternatingFive {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) (σ : MulAut X) (hσ : σ * σ = 1) (c : X)
    (hc : orderOf c = 5) (hσc : σ c = c) : σ = 1 := by
  open CFSG.Semidihedral.Principal.CyclicAlternatingFive in
  obtain ⟨π, hπ⟩ := conjNormal_surjective (MulAut.congr e σ)
  open CFSG.Semidihedral.Principal.CyclicAlternatingFive in
  have hπ2 : π * π = 1 := by
    apply conjNormal_injective
    rw [map_mul, hπ, map_one, ← map_mul, hσ, map_one]
  have hc' : orderOf (e c) = 5 := by rw [MulEquiv.orderOf_eq, hc]
  have hfix : π * ((e c : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = e c * π := by
    have h := congrArg (fun φ : MulAut (alternatingGroup (Fin 5)) =>
      ((φ (e c) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) hπ
    simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hσc] at h
    calc π * ((e c : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))
        = (π * ((e c : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * π⁻¹) * π := by group
      _ = e c * π := by rw [h]
  have hπ1 : π = 1 := perm_five_eq_one_of_conj π (e c) hπ2
    (by have := pow_orderOf_eq_one (e c); rwa [hc'] at this)
    (fun h1 => by rw [h1, orderOf_one] at hc'; omega) hfix
  have h1 : MulAut.congr e σ = 1 := by rw [← hπ, hπ1, map_one]
  exact (MulAut.congr e).injective (h1.trans (map_one _).symm)

theorem mulAut_eq_one_of_alternatingFour {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 4)) (σ : MulAut X) (hσ : σ * σ = 1) (c : X)
    (hc : orderOf c = 3) (hσc : σ c = c) : σ = 1 := by
  open CFSG.Semidihedral.Principal.CyclicSymmetricFour in
  obtain ⟨π, hπ⟩ := conjNormal_surjective (MulAut.congr e σ)
  open CFSG.Semidihedral.Principal.CyclicSymmetricFour in
  have hπ2 : π * π = 1 := by
    apply conjNormal_injective
    rw [map_mul, hπ, map_one, ← map_mul, hσ, map_one]
  have hc' : orderOf (e c) = 3 := by rw [MulEquiv.orderOf_eq, hc]
  have hfix : π * ((e c : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) = e c * π := by
    have h := congrArg (fun φ : MulAut (alternatingGroup (Fin 4)) =>
      ((φ (e c) : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))) hπ
    simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hσc] at h
    calc π * ((e c : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))
        = (π * ((e c : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) * π⁻¹) * π := by group
      _ = e c * π := by rw [h]
  have hπ1 : π = 1 := perm_four_eq_one_of_conj π (e c) hπ2
    (by have := pow_orderOf_eq_one (e c); rwa [hc'] at this)
    (fun h1 => by rw [h1, orderOf_one] at hc'; omega) hfix
  have h1 : MulAut.congr e σ = 1 := by rw [← hπ, hπ1, map_one]
  exact (MulAut.congr e).injective (h1.trans (map_one _).symm)

theorem mulAut_fix_alternating_of_symmetricFour {X : Type*} [Group X]
    (e : X ≃* Equiv.Perm (Fin 4)) (σ : MulAut X) (hσ : σ * σ = 1) (c : X)
    (hc : orderOf c = 3) (hσc : σ c = c) :
    ∀ x : X, e x ∈ alternatingGroup (Fin 4) → σ x = x := by
  set σ' := MulAut.congr e σ with hσ'
  have hσ'apply : ∀ y, σ' y = e (σ (e.symm y)) := fun y => rfl
  have hsign : Equiv.Perm.sign.comp σ'.toMonoidHom = Equiv.Perm.sign := by
    apply Equiv.Perm.eq_sign_of_surjective_hom
    intro u
    obtain ⟨y, rfl⟩ := Equiv.Perm.sign_surjective (Fin 4) u
    exact ⟨σ'.symm y, by simp⟩
  have hsign' : ∀ x, Equiv.Perm.sign (σ' x) = Equiv.Perm.sign x := fun x =>
    congrArg (fun φ : Equiv.Perm (Fin 4) →* ℤˣ => φ x) hsign
  have hA : (alternatingGroup (Fin 4)).map σ'.toMonoidHom = alternatingGroup (Fin 4) := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Equiv.Perm.mem_alternatingGroup] at hx ⊢
      rw [MulEquiv.coe_toMonoidHom, hsign', hx]
    · intro hy
      refine ⟨σ'.symm y, ?_, by simp⟩
      rw [Equiv.Perm.mem_alternatingGroup] at hy ⊢
      rw [← hsign', MulEquiv.apply_symm_apply, hy]
  let β : MulAut (alternatingGroup (Fin 4)) :=
    (σ'.subgroupMap (alternatingGroup (Fin 4))).trans (MulEquiv.subgroupCongr hA)
  have hβ : ∀ a : alternatingGroup (Fin 4), (β a : Equiv.Perm (Fin 4)) = σ' a := fun a => rfl
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun φ : MulAut X => φ x) hσ
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hβ, hβ, hσ'apply, hσ'apply, MulEquiv.symm_apply_apply,
      hσσ, MulEquiv.apply_symm_apply]
  have hcA : e c ∈ alternatingGroup (Fin 4) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    apply perm_four_sign_of_pow_three
    rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
  have hβc : β ⟨e c, hcA⟩ = ⟨e c, hcA⟩ := by
    apply Subtype.ext
    rw [hβ, hσ'apply, MulEquiv.symm_apply_apply, hσc]
  have hord : orderOf (⟨e c, hcA⟩ : alternatingGroup (Fin 4)) = 3 := by
    rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hc]
  have hβ1 := mulAut_eq_one_of_alternatingFour (MulEquiv.refl _) β hβ2 _ hord hβc
  intro x hx
  have h := congrArg (fun φ : MulAut (alternatingGroup (Fin 4)) =>
    ((φ ⟨e x, hx⟩ : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))) hβ1
  simp only [MulAut.one_apply] at h
  rw [hβ, hσ'apply, MulEquiv.symm_apply_apply] at h
  exact e.injective h

theorem exists_mulAut_of_conj {Y X : Type*} [Group Y] [Group X] (U : Subgroup Y)
    (θ : U →* X) (hθ : Function.Surjective θ) (g : Y) (hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hg2 : g * g = 1) (hker : ∀ u : U, θ u = 1 → θ ⟨g * u * g⁻¹, hgU u u.2⟩ = 1) :
    ∃ σ : MulAut X, σ * σ = 1 ∧ ∀ u : U, σ (θ u) = θ ⟨g * u * g⁻¹, hgU u u.2⟩ := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  let α : MulAut U :=
    { toFun := fun u => ⟨g * u * g⁻¹, hgU u u.2⟩
      invFun := fun u => ⟨g * u * g⁻¹, hgU u u.2⟩
      left_inv := fun u => Subtype.ext (by
        change g * (g * (u : Y) * g⁻¹) * g⁻¹ = u
        rw [hginv, ← mul_assoc, ← mul_assoc, hg2, one_mul, mul_assoc, hg2, mul_one])
      right_inv := fun u => Subtype.ext (by
        change g * (g * (u : Y) * g⁻¹) * g⁻¹ = u
        rw [hginv, ← mul_assoc, ← mul_assoc, hg2, one_mul, mul_assoc, hg2, mul_one])
      map_mul' := fun u v => Subtype.ext (by
        change g * ((u : Y) * v) * g⁻¹ = g * u * g⁻¹ * (g * v * g⁻¹)
        group) }
  have hαα : ∀ u, α (α u) = u := fun u => α.left_inv u
  have hmap : θ.ker.map (α : U →* U) = θ.ker := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hker v hv
    · intro hu
      exact ⟨α u, hker u hu, hαα u⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let σ : MulAut X := e.symm.trans ((QuotientGroup.congr θ.ker θ.ker α hmap).trans e)
  have hσ : ∀ u : U, σ (θ u) = θ (α u) := by
    intro u
    have h1 : e.symm (θ u) = (u : U ⧸ θ.ker) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change e (QuotientGroup.congr θ.ker θ.ker α hmap (e.symm (θ u))) = θ (α u)
    rw [h1, QuotientGroup.congr_mk]
    rfl
  refine ⟨σ, ?_, hσ⟩
  ext x
  obtain ⟨u, rfl⟩ := hθ x
  rw [MulAut.mul_apply, MulAut.one_apply, hσ, hσ, hαα]

theorem card_le_card_centralizer_of_conj_mem_zpowers {Y : Type*} [Group Y] [Finite Y]
    (U : Subgroup Y) (g z : Y) (hz : z ∈ Subgroup.center Y) (hz2 : z * z = 1) (hgU : g ∉ U)
    (h : ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ Subgroup.zpowers z) :
    Nat.card U ≤ Nat.card (Subgroup.centralizer ({g} : Set Y)) := by
  have hcen : ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ Subgroup.center Y := fun u hu =>
    (Subgroup.zpowers_le.mpr hz) (h u hu)
  let χ : U →* Y :=
    { toFun := fun u => g * u * g⁻¹ * u⁻¹
      map_one' := by simp
      map_mul' := fun u v => by
        have hv := Subgroup.mem_center_iff.mp (hcen v v.2)
        change g * ((u : Y) * v) * g⁻¹ * ((u : Y) * v)⁻¹ =
          g * u * g⁻¹ * (u : Y)⁻¹ * (g * v * g⁻¹ * (v : Y)⁻¹)
        have hu := Subgroup.mem_center_iff.mp (hcen u u.2)
        calc g * ((u : Y) * v) * g⁻¹ * ((u : Y) * v)⁻¹
            = g * u * g⁻¹ * ((g * v * g⁻¹ * (v : Y)⁻¹) * (u : Y)⁻¹) := by group
          _ = g * u * g⁻¹ * ((u : Y)⁻¹ * (g * v * g⁻¹ * (v : Y)⁻¹)) := by
            rw [hv (u : Y)⁻¹]
          _ = g * u * g⁻¹ * (u : Y)⁻¹ * (g * v * g⁻¹ * (v : Y)⁻¹) := by group }
  have hrange : Nat.card χ.range ≤ 2 := by
    have hle : χ.range ≤ Subgroup.zpowers z := by
      rintro _ ⟨u, rfl⟩
      exact h u u.2
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, hz2])
  let K : Subgroup Y := χ.ker.map U.subtype
  have hKcard : Nat.card K = Nat.card χ.ker :=
    Subgroup.card_map_of_injective U.subtype_injective
  have hKC : K ≤ Subgroup.centralizer ({g} : Set Y) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * (u : Y) * g⁻¹ * (u : Y)⁻¹ = 1 := hu
    change (u : Y) * g = g * u
    calc (u : Y) * g = (g * (u : Y) * g⁻¹ * (u : Y)⁻¹)⁻¹ * (g * u) := by group
      _ = g * u := by rw [h1, inv_one, one_mul]
  have hKU : K ≤ U := Subgroup.map_subtype_le _
  have hgK : g ∉ K := fun hg => hgU (hKU hg)
  have hgC : g ∈ Subgroup.centralizer ({g} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hidx : 2 ≤ (K.subgroupOf (Subgroup.centralizer ({g} : Set Y))).index := by
    have hne : K.subgroupOf (Subgroup.centralizer ({g} : Set Y)) ≠ ⊤ := by
      intro htop
      apply hgK
      have : (⟨g, hgC⟩ : Subgroup.centralizer ({g} : Set Y)) ∈
          K.subgroupOf (Subgroup.centralizer ({g} : Set Y)) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact this
    rcases Nat.lt_or_ge (K.subgroupOf (Subgroup.centralizer ({g} : Set Y))).index 2 with
      hlt | hge
    · exfalso
      have h0 := Subgroup.index_ne_zero_of_finite
        (H := K.subgroupOf (Subgroup.centralizer ({g} : Set Y)))
      have h1 : (K.subgroupOf (Subgroup.centralizer ({g} : Set Y))).index = 1 := by omega
      exact hne (Subgroup.index_eq_one.mp h1)
    · exact hge
  have hcardC := Subgroup.card_mul_index (K.subgroupOf (Subgroup.centralizer ({g} : Set Y)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv] at hcardC
  have hU := card_ker_mul_card_range χ
  rw [← hKcard] at hU
  have h2K : Nat.card U ≤ 2 * Nat.card K := by
    rw [← hU]
    nlinarith
  nlinarith

end SL2Sections

end CFSG.Semidihedral.AllPrime

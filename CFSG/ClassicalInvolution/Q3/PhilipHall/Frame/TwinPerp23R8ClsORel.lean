module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOCtr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

theorem eq_one_of_sq_of_odd {G : Type*} [Group G] {x : G} (h2 : x * x = 1) {N : ℕ} (hN : Odd N)
    (hx : x ^ N = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hN
  have h : x ^ (2 * k + 1) = x := by rw [pow_succ, pow_mul, pow_two, h2, one_pow, one_mul]
  rw [← h]
  exact hx

theorem piC_conj_oddCore {Y : Type} [Group Y] [Finite Y] (C : Subgroup Y) {o x : Y}
    (ho : o ∈ oddCoreOf C) (hx : x ∈ C) (hox : o * x * o⁻¹ ∈ C) :
    F7I.piC C ⟨o * x * o⁻¹, hox⟩ = F7I.piC C ⟨x, hx⟩ := by
  have hoC : o ∈ C := (oddCoreOf_normalized C).2 ho
  have h1 : F7I.piC C ⟨o, hoC⟩ = 1 := (F7I.piC_eq_one_iff _).mpr ho
  rw [show (⟨o * x * o⁻¹, hox⟩ : ↥C) = ⟨o, hoC⟩ * ⟨x, hx⟩ * (⟨o, hoC⟩ : ↥C)⁻¹ from Subtype.ext rfl,
    map_mul, map_mul, map_inv, h1, one_mul, inv_one, mul_one]

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem E_prod_eq (hc : P23Cfg n Y R S t K' W u e g) {Z : Subgroup Y} (hZ : P23ZData t u e Z) {y m : Y}
    (hyt : y * t = t * y) {N : ℕ} (hN : Odd N) (hmN : m ^ N = 1) (hmu : m * u = u * m)
    (hrel : e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) = t * m ∨
      e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) = u * t * m)
    {o nn E : ℕ → Y} (ho : ∀ i, o i ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)))
    (hnn : ∀ i, nn i ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y))
    (hy : ∀ i : ℕ, y ^ i = o i * nn i) (hE : ∀ i, E i = nn i * e * (nn i)⁻¹) :
    E 0 * E 1 * E 2 = t := by
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hd := hc.data
  have hz : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hut : u * t = t * u := hWab _ hd.huW _ hd.hzW
  have het : e * t = t * e := hWab _ heW _ hd.hzW
  have ht2 : t * t = 1 := hz.sq
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr het
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hyt
  have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hut
  have hy2C : y ^ 2 ∈ C := C.pow_mem hyC 2
  have he1C : y * e * y⁻¹ ∈ C := C.mul_mem (C.mul_mem hyC heC) (C.inv_mem hyC)
  have he2C : y ^ 2 * e * (y ^ 2)⁻¹ ∈ C := C.mul_mem (C.mul_mem hy2C heC) (C.inv_mem hy2C)
  have hXC : e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) ∈ C :=
    C.mul_mem (C.mul_mem heC he1C) he2C
  have hmC : m ∈ C := by
    rcases hrel with h | h
    · have : m = t⁻¹ * (e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹)) := by rw [h]; group
      rw [this]
      exact C.mul_mem (C.inv_mem htC) hXC
    · have : m = (u * t)⁻¹ * (e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹)) := by rw [h]; group
      rw [this]
      exact C.mul_mem (C.inv_mem (C.mul_mem huC htC)) hXC
  have hEZ : ∀ i, E i ∈ Z := fun i => by
    rw [hE i]
    exact (Subgroup.mem_normalizer_iff.mp (hnn i).2 e).mp hZ.he
  have hEC : ∀ i, E i ∈ C := fun i => hZ.le_t (hEZ i)
  have hpi : ∀ (i : ℕ) (c : ↥C), (c : Y) = y ^ i * e * (y ^ i)⁻¹ →
      F7I.piC C c = F7I.piC C ⟨E i, hEC i⟩ := by
    intro i c hci
    have h1 : (c : Y) = o i * E i * (o i)⁻¹ := by rw [hci, hy i, hE i]; group
    have hoC : o i ∈ C := (oddCoreOf_normalized C).2 (ho i)
    have hox : o i * E i * (o i)⁻¹ ∈ C := C.mul_mem (C.mul_mem hoC (hEC i)) (C.inv_mem hoC)
    rw [← piC_conj_oddCore C (ho i) (hEC i) hox]
    exact congrArg _ (Subtype.ext h1)
  have h0 : F7I.piC C ⟨e, heC⟩ = F7I.piC C ⟨E 0, hEC 0⟩ := hpi 0 ⟨e, heC⟩ (by simp)
  have h1 : F7I.piC C ⟨y * e * y⁻¹, he1C⟩ = F7I.piC C ⟨E 1, hEC 1⟩ := hpi 1 ⟨_, he1C⟩ (by simp)
  have h2 : F7I.piC C ⟨y ^ 2 * e * (y ^ 2)⁻¹, he2C⟩ = F7I.piC C ⟨E 2, hEC 2⟩ := hpi 2 ⟨_, he2C⟩ rfl
  have key : ∀ (ζ : Y) (hζZ : ζ ∈ Z) (hζC : ζ ∈ C),
      F7I.piC C ⟨ζ, hζC⟩ = F7I.piC C ⟨e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹), hXC⟩ → ζ = t := by
    intro ζ hζZ hζC hζπ
    have hwZ : ζ * t ∈ Z := Z.mul_mem hζZ hZ.ht
    have hwC : ζ * t ∈ C := hZ.le_t hwZ
    have hw2 : (ζ * t) * (ζ * t) = 1 := hZ.sq _ hwZ
    have htm : (⟨t, htC⟩ : ↥C) * ⟨m, hmC⟩ = ⟨m, hmC⟩ * ⟨t, htC⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hmC).symm
    have htt : (⟨t, htC⟩ : ↥C) * ⟨t, htC⟩ = 1 := Subtype.ext ht2
    have hπw : F7I.piC C ⟨ζ * t, hwC⟩ = F7I.piC C ⟨ζ, hζC⟩ * F7I.piC C ⟨t, htC⟩ := by
      rw [← map_mul]
      rfl
    have hπm : (F7I.piC C ⟨m, hmC⟩) ^ N = 1 := by
      rw [← map_pow]
      have : (⟨m, hmC⟩ : ↥C) ^ N = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hmN)
      rw [this, map_one]
    have hππ : F7I.piC C ⟨ζ * t, hwC⟩ * F7I.piC C ⟨ζ * t, hwC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨ζ * t, hwC⟩ : ↥C) * ⟨ζ * t, hwC⟩ = 1 := Subtype.ext hw2
      rw [this, map_one]
    rcases hrel with hB | hA
    ·
      have hX : (⟨e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹), hXC⟩ : ↥C) = ⟨t, htC⟩ * ⟨m, hmC⟩ :=
        Subtype.ext hB
      rw [hX, map_mul] at hζπ
      have hwm : F7I.piC C ⟨ζ * t, hwC⟩ = F7I.piC C ⟨m, hmC⟩ := by
        calc F7I.piC C ⟨ζ * t, hwC⟩ = F7I.piC C ⟨ζ, hζC⟩ * F7I.piC C ⟨t, htC⟩ := hπw
          _ = F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨t, htC⟩ := by rw [hζπ]
          _ = F7I.piC C ((⟨t, htC⟩ : ↥C) * ⟨m, hmC⟩ * ⟨t, htC⟩) := by simp only [map_mul]
          _ = F7I.piC C ⟨m, hmC⟩ := by
            congr 1
            calc (⟨t, htC⟩ : ↥C) * ⟨m, hmC⟩ * ⟨t, htC⟩ = ⟨m, hmC⟩ * ⟨t, htC⟩ * ⟨t, htC⟩ := by rw [htm]
              _ = ⟨m, hmC⟩ * (⟨t, htC⟩ * ⟨t, htC⟩) := mul_assoc _ _ _
              _ = ⟨m, hmC⟩ := by rw [htt, mul_one]
      have hm1 : F7I.piC C ⟨m, hmC⟩ = 1 :=
        eq_one_of_sq_of_odd (by rw [← hwm]; exact hππ) hN hπm
      have hw1 : F7I.piC C ⟨ζ * t, hwC⟩ = 1 := by rw [hwm, hm1]
      have hwO : ζ * t ∈ oddCoreOf C := (F7I.piC_eq_one_iff _).mp hw1
      have hbot : ζ * t ∈ Z ⊓ oddCoreOf C := Subgroup.mem_inf.mpr ⟨hwZ, hwO⟩
      rw [hZ.inf_oddCoreOf_eq_bot, Subgroup.mem_bot] at hbot
      calc ζ = ζ * t * t := by rw [mul_assoc, ht2, mul_one]
        _ = t := by rw [hbot, one_mul]
    ·
      exfalso
      have hX : (⟨e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹), hXC⟩ : ↥C) =
          ⟨u, huC⟩ * ⟨t, htC⟩ * ⟨m, hmC⟩ := Subtype.ext hA
      rw [hX] at hζπ
      simp only [map_mul] at hζπ
      have humC : (⟨u, huC⟩ : ↥C) * ⟨m, hmC⟩ = ⟨m, hmC⟩ * ⟨u, huC⟩ := Subtype.ext hmu.symm
      have huu : (⟨u, huC⟩ : ↥C) * ⟨u, huC⟩ = 1 := Subtype.ext hd.hu2
      have hwm : F7I.piC C ⟨ζ * t, hwC⟩ = F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨m, hmC⟩ := by
        calc F7I.piC C ⟨ζ * t, hwC⟩ = F7I.piC C ⟨ζ, hζC⟩ * F7I.piC C ⟨t, htC⟩ := hπw
          _ = F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨t, htC⟩ := by
            rw [hζπ]
          _ = F7I.piC C ((⟨u, huC⟩ : ↥C) * ⟨t, htC⟩ * ⟨m, hmC⟩ * ⟨t, htC⟩) := by simp only [map_mul]
          _ = F7I.piC C ((⟨u, huC⟩ : ↥C) * ⟨m, hmC⟩) := by
            congr 1
            calc (⟨u, huC⟩ : ↥C) * ⟨t, htC⟩ * ⟨m, hmC⟩ * ⟨t, htC⟩
                = ⟨u, huC⟩ * (⟨t, htC⟩ * ⟨m, hmC⟩) * ⟨t, htC⟩ := by group
              _ = ⟨u, huC⟩ * (⟨m, hmC⟩ * ⟨t, htC⟩) * ⟨t, htC⟩ := by rw [htm]
              _ = ⟨u, huC⟩ * ⟨m, hmC⟩ * (⟨t, htC⟩ * ⟨t, htC⟩) := by group
              _ = ⟨u, huC⟩ * ⟨m, hmC⟩ := by rw [htt, mul_one]
          _ = F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨m, hmC⟩ := by simp only [map_mul]
      have hab : F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨m, hmC⟩ = F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨u, huC⟩ := by
        rw [← map_mul, ← map_mul, humC]
      have haa : F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨u, huC⟩ = 1 := by
        rw [← map_mul, huu, map_one]
      have hbb : F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨m, hmC⟩ = 1 := by
        calc F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨m, hmC⟩
            = (F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨u, huC⟩) * (F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨m, hmC⟩) := by
              rw [haa, one_mul]
          _ = F7I.piC C ⟨u, huC⟩ * (F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨m, hmC⟩) * F7I.piC C ⟨m, hmC⟩ := by group
          _ = F7I.piC C ⟨u, huC⟩ * (F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨u, huC⟩) * F7I.piC C ⟨m, hmC⟩ := by
            rw [hab]
          _ = (F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨m, hmC⟩) * (F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨m, hmC⟩) := by
            group
          _ = 1 := by rw [← hwm]; exact hππ
      have hm1 : F7I.piC C ⟨m, hmC⟩ = 1 := eq_one_of_sq_of_odd hbb hN hπm
      have hwu : F7I.piC C ⟨ζ * t, hwC⟩ = F7I.piC C ⟨u, huC⟩ := by rw [hwm, hm1, mul_one]
      obtain ⟨hU1, -, h8, -, hnc, -, hcomm, -, -, b₁, b', hbb', hb₁K, hb'K', hb₁1, hb₁t, -, -⟩ :=
        p23_twin_q8 hc hCdef htC heC
      have hcent := (p23_zdata_cent_twins hc hZ hCdef hwZ hwC).1
      have hπu : F7I.piC C ⟨u, huC⟩ = F7I.piC C b₁ * F7I.piC C b' := by
        rw [← map_mul]
        exact congrArg _ (Subtype.ext hbb'.symm)
      have hcen : ∀ x ∈ ((tightCore R).subgroupOf C).map (F7I.piC C),
          F7I.piC C b₁ * x = x * F7I.piC C b₁ := by
        intro x hx
        have h1 := hcent x hx
        rw [hwu, hπu] at h1
        have h2 : x * F7I.piC C b' = F7I.piC C b' * x := hcomm x hx _ hb'K'
        apply mul_right_cancel (b := F7I.piC C b')
        calc F7I.piC C b₁ * x * F7I.piC C b' = F7I.piC C b₁ * (x * F7I.piC C b') := mul_assoc _ _ _
          _ = F7I.piC C b₁ * (F7I.piC C b' * x) := by rw [h2]
          _ = (F7I.piC C b₁ * F7I.piC C b') * x := (mul_assoc _ _ _).symm
          _ = x * (F7I.piC C b₁ * F7I.piC C b') := h1
          _ = x * F7I.piC C b₁ * F7I.piC C b' := (mul_assoc _ _ _).symm
      rcases eq_one_or_eq_of_central h8 hnc hU1.unique hb₁K hcen with h | h
      · exact hb₁1 h
      · exact hb₁t h
  have hζZ : E 0 * E 1 * E 2 ∈ Z := Z.mul_mem (Z.mul_mem (hEZ 0) (hEZ 1)) (hEZ 2)
  have hζC : E 0 * E 1 * E 2 ∈ C := hZ.le_t hζZ
  refine key _ hζZ hζC ?_
  have e1 : (⟨E 0 * E 1 * E 2, hζC⟩ : ↥C) = ⟨E 0, hEC 0⟩ * ⟨E 1, hEC 1⟩ * ⟨E 2, hEC 2⟩ :=
    Subtype.ext rfl
  have e2 : (⟨e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹), hXC⟩ : ↥C) =
      ⟨e, heC⟩ * ⟨y * e * y⁻¹, he1C⟩ * ⟨y ^ 2 * e * (y ^ 2)⁻¹, he2C⟩ := Subtype.ext rfl
  rw [e1, e2]
  simp only [map_mul]
  rw [h0, h1, h2]

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

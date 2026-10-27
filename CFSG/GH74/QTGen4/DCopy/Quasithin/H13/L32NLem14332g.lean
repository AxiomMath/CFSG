module

public import CFSG.Quasithin.H13.L32NLem14332g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement MatrixGroups

namespace L14332

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)}

theorem Ctx14332.exists_sq_ne_of_case_ii_F4 (h1288 : Lemma12_8_8_two_F4) (hKG : KGL24Quad)
    (C : Ctx14332 G T L V V₂ g a D) (hii : Case14323ii T V g D) :
    ∃ y ∈ centerOf (fsuU T V), y * y ≠ 1 := by
  by_contra hall
  push Not at hall
  obtain ⟨-, -, -, hq⟩ := h1288 G T L V 3 (fsuV1 T V) V₂ C.setting D
  obtain ⟨q, -, hpol, hinv⟩ := hq (frattiniOf_eq_bot_of_sq (zU_comm _) hall)
  have hq0 := not_quadratic_of_case_ii hKG hii.natural hpol hinv

  apply C.pi_ne
  refine L128A.HatU.B_nondegenerate D (D.π a) fun w => ?_
  have := hpol (D.π a) w
  rw [hq0, hq0, hq0, zero_add, zero_add] at this
  exact this.symm

theorem Ctx14332.z4q8q8_of_case_ii_F4 (h1288 : Lemma12_8_8_two_F4) (hKG : KGL24Quad)
    (C : Ctx14332 G T L V V₂ g a D) (hii : Case14323ii T V g D)
    (h4 : Nat.card ↥(centerOf (fsuU T V)) = 4) (hd : Module.finrank (ZMod 2) D.V = 4) :
    HSType.IsZ4Q8Q8 ↥(fsuU T V) := by
  obtain ⟨c, hcZ, hcc1⟩ := C.exists_sq_ne_of_case_ii_F4 h1288 hKG hii
  obtain ⟨hcU, hcC⟩ := Subgroup.mem_inf.mp hcZ

  obtain ⟨⟨z, hzV⟩, hz1, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp C.card_V1
  have hz : z ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hV1 : ∀ x ∈ fsuV1 T V, x = 1 ∨ x = z := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp C.card_V1
      have e1 := hy ⟨x, hx⟩ (fun h0 => hx1 (congrArg Subtype.val h0))
      have e2 := hy ⟨z, hzV⟩ hz1
      exact congrArg Subtype.val (e1.trans e2.symm)
  have hzz : z * z = 1 := by
    have := pow_card_eq_one' (G := ↥(fsuV1 T V)) (x := ⟨z, hzV⟩)
    rw [C.card_V1, pow_two] at this
    exact congrArg Subtype.val this
  have hcc : c * c = z := (hV1 _ (C.sq c hcU)).resolve_left hcc1
  have hzZ : z ∈ centerOf (fsuU T V) := C.lt.le hzV
  have S : Q8Pow.CommPair z (fsuU T V) :=
    { z_mem := (Subgroup.mem_inf.mp hzZ).1
      z_ne := hz
      z_sq := hzz
      z_comm := fun u hu =>
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZ).2 u hu
      comm := fun u hu w hw => hV1 _ (C.comm u hu w hw)
      sq := fun u hu => hV1 _ (C.sq u hu) }
  have hcZ' : ∀ u ∈ fsuU T V, c * u = u * c := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp hcC u hu).symm

  have hZc : centerOf (fsuU T V) = Subgroup.zpowers c := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcZ) ?_).symm
    rw [h4, Nat.card_zpowers]
    have hc4 : c ^ 4 = 1 := by
      calc c ^ 4 = (c * c) * (c * c) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [hcc, hzz]
    have hdvd : orderOf c ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hc4
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hk'
      exact absurd (by rw [hk', one_mul]) hcc1
    · rw [pow_one] at hk'
      exact absurd (by rw [← pow_two, ← hk', pow_orderOf_eq_one]) hcc1
    · rw [hk']; norm_num
  have hcen : ∀ u ∈ fsuU T V, (∀ w ∈ fsuU T V, u * w = w * u) → u ∈ Subgroup.zpowers c := by
    intro u hu h
    rw [← hZc]
    exact Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_iff.mpr fun w hw => (h w hw).symm⟩

  have hcard : Nat.card ↥(fsuU T V) = 64 := by
    rw [D.card_U, h4]
    have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd, Nat.card_zmod]
    norm_num
  exact Q8Pow.nonempty_mulEquiv_z4Q8Q8 S hcU hcc hcZ' hcen hcard

end L14332

end CFSG.Quasithin.H13

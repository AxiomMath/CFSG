module

public import CFSG.LargeExtraspecial.S111ABasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}

omit [Finite G] in
theorem exists_adjoin_involution (A : Subgroup G) {β : G} (hβ : β * β = 1)
    (hc : ∀ x ∈ A, x * β = β * x) :
    ∃ B : Subgroup G, A ≤ B ∧ β ∈ B ∧ ∀ x ∈ B, x ∈ A ∨ x * β ∈ A := by
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ
  have hc' : ∀ x, x * β ∈ A → x * β = β * x := fun x hx => by
    have h1 := hc _ hx
    calc x * β = x * β * β * β := by rw [mul_assoc (x * β), hβ, mul_one]
      _ = β * (x * β) * β := by rw [h1]
      _ = β * x * (β * β) := by simp only [mul_assoc]
      _ = β * x := by rw [hβ, mul_one]
  refine ⟨{ carrier := {x | x ∈ A ∨ x * β ∈ A}
            mul_mem' := ?_
            one_mem' := Or.inl A.one_mem
            inv_mem' := ?_ }, fun x hx => Or.inl hx, Or.inr (by rw [hβ]; exact A.one_mem),
          fun x hx => hx⟩
  · rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (A.mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact A.mul_mem hx hy)
    · refine Or.inr ?_
      have e : x * y * β = x * β * y := by rw [mul_assoc, hc y hy, ← mul_assoc]
      rw [e]
      exact A.mul_mem hx hy
    · refine Or.inl ?_
      have e : x * y = x * β * (y * β) := by
        rw [hc' y hy, ← mul_assoc, mul_assoc x β β, hβ, mul_one]
      rw [e]
      exact A.mul_mem hx hy
  · rintro x (hx | hx)
    · exact Or.inl (A.inv_mem hx)
    · refine Or.inr ?_
      have e : x⁻¹ * β = (x * β)⁻¹ := by
        rw [hc' x hx, mul_inv_rev, hβi]
      rw [e]
      exact A.inv_mem hx

theorem IncClosed.two_point (hy : Hyp S g) (hA : IncClosed S A) {k i j : G}
    (hk : k * S.z * k⁻¹ ∈ A) (hkz : k * S.z * k⁻¹ ≠ S.z) (hi : i * S.z * i⁻¹ ∈ A)
    (hjQ : j * S.z * j⁻¹ ∈ S.QG) (hjk : j * S.z * j⁻¹ ∈ S.Qa k)
    (hji : j * S.z * j⁻¹ ∉ S.Qa i) : Timmesfeld11_1Stmt S := by
  have hαQ : k * S.z * k⁻¹ ∈ S.QG := hA.le_QG hk
  have hαi : k * S.z * k⁻¹ ∈ S.Qa i := hA.le_Qa i hi hk
  have hzi : S.z ∈ S.Qa i := hA.le_Qa i hi hA.z_mem
  have huz : i * S.z * i⁻¹ ≠ S.z := fun h => hji (by rw [S.Qa_eq_QG_of_conj_eq h]; exact hjQ)
  have huα : i * S.z * i⁻¹ ≠ k * S.z * k⁻¹ := fun h =>
    hji (by rw [S.Qa_eq_of_conj_eq h]; exact hjk)
  have huαz : i * S.z * i⁻¹ ≠ k * S.z * k⁻¹ * S.z := fun h =>
    hji ((QG_inf_Qa_eq_of_mul_z hαQ hkz h).ge ⟨hjQ, hjk⟩).2
  have hcomm : j * S.z * j⁻¹ * (i * S.z * i⁻¹) = i * S.z * i⁻¹ * (j * S.z * j⁻¹) :=
    S.QG_inf_Qa_comm hkz ⟨hjQ, hjk⟩ ⟨hA.le_QG hi, hA.le_Qa k hk hi⟩
  have hne : ∀ x y : G, x ≠ y → i⁻¹ * x * i ≠ i⁻¹ * y * i := fun x y hxy h =>
    hxy (mul_left_cancel (mul_right_cancel h))
  have e0 : i⁻¹ * (i * S.z * i⁻¹) * i = S.z := by group
  have e1 : i⁻¹ * S.z * i⁻¹⁻¹ = i⁻¹ * S.z * i := by rw [inv_inv]
  have e2 : (i⁻¹ * k) * S.z * (i⁻¹ * k)⁻¹ = i⁻¹ * (k * S.z * k⁻¹) * i := by group
  have e3 : (i⁻¹ * j) * S.z * (i⁻¹ * j)⁻¹ = i⁻¹ * (j * S.z * j⁻¹) * i := by group
  refine exists_of_two_points hy (k := i⁻¹) (j := i⁻¹ * k) (u := i⁻¹ * j) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · rw [e1]
    exact (mem_Qa_iff_conj i _).mp hzi
  · rw [e1]
    conv_rhs => rw [← e0]
    exact hne _ _ huz.symm
  · rw [e2]
    exact (mem_Qa_iff_conj i _).mp hαi
  · rw [e2]
    conv_rhs => rw [← e0]
    exact hne _ _ huα.symm
  · rw [e1, e2]
    exact hne _ _ hkz
  · rw [e1, e2]
    have e4 : i⁻¹ * S.z * i * S.z = i⁻¹ * (S.z * (i * S.z * i⁻¹)) * i := by group
    rw [e4]
    refine hne _ _ fun h => huαz ?_
    have hzu := S.z_comm_QG (hA.le_QG hi)
    calc i * S.z * i⁻¹ = S.z * S.z * (i * S.z * i⁻¹) := by rw [S.z_mul_z, one_mul]
      _ = S.z * (i * S.z * i⁻¹ * S.z) := by rw [hzu]; exact mul_assoc _ _ _
      _ = k * S.z * k⁻¹ * S.z := by rw [h]; exact (mul_assoc _ _ _).symm
  · rw [e3]
    refine S.mem_M_iff.mpr ?_
    calc i⁻¹ * (j * S.z * j⁻¹) * i * S.z
        = i⁻¹ * (j * S.z * j⁻¹ * (i * S.z * i⁻¹)) * i := by group
      _ = i⁻¹ * (i * S.z * i⁻¹ * (j * S.z * j⁻¹)) * i := by rw [hcomm]
      _ = S.z * (i⁻¹ * (j * S.z * j⁻¹) * i) := by group
  · rw [e3]
    exact fun h => hji ((mem_Qa_iff_conj i _).mpr h)
  · rw [e3, mem_Qa_iff_conj]
    convert hjQ using 1
    group
  · rw [e3, mem_Qa_iff_conj]
    convert (mem_Qa_iff_conj k _).mp hjk using 1
    group

theorem IncClosed.exists_adjoin (hA : IncClosed S A) {j : G} (hjQ : j * S.z * j⁻¹ ∈ S.QG)
    (hjA : j * S.z * j⁻¹ ∉ A) (hall : ∀ i : G, i * S.z * i⁻¹ ∈ A → j * S.z * j⁻¹ ∈ S.Qa i) :
    ∃ B : Subgroup G, IncClosed S B ∧ A ≤ B ∧ j * S.z * j⁻¹ ∈ B := by
  have hβ2 : j * S.z * j⁻¹ * (j * S.z * j⁻¹) = 1 := (S.conjBy j).z_mul_z
  have hc : ∀ x ∈ A, x * (j * S.z * j⁻¹) = j * S.z * j⁻¹ * x := fun x hx => by
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, mul_one]
    obtain ⟨i, rfl⟩ := hA.conj x hx hx1
    exact (commute_of_mem_Qa (hall i hx)).symm
  have hββ : ∀ x : G, x = x * (j * S.z * j⁻¹) * (j * S.z * j⁻¹) := fun x => by
    rw [mul_assoc x, hβ2, mul_one]
  obtain ⟨B, hAB, hβB, hB⟩ := exists_adjoin_involution A hβ2 hc
  refine ⟨B, ⟨fun x hx => ?_, hAB hA.z_mem, fun x hx hx1 => ?_, fun i hi => ?_⟩, hAB, hβB⟩
  · rcases hB x hx with h | h
    · exact hA.le_QG h
    · rw [hββ x]
      exact S.QG.mul_mem (hA.le_QG h) hjQ
  · rcases hB x hx with h | h
    · exact hA.conj x h hx1
    by_cases hu1 : x * (j * S.z * j⁻¹) = 1
    · exact ⟨j, by rw [hββ x, hu1, one_mul]⟩
    obtain ⟨i, hi⟩ := hA.conj _ h hu1
    have hiA : i * S.z * i⁻¹ ∈ A := hi ▸ h
    have hβne : j * S.z * j⁻¹ ≠ i * S.z * i⁻¹ := fun e => hjA (by rw [e]; exact hiA)
    obtain ⟨q, -, hqβ⟩ :=
      (S.conjBy i).exists_conj_eq_mul_z (hall i hiA) (conj_z_ne_one S j) hβne
    refine ⟨q * j, ?_⟩
    calc x = x * (j * S.z * j⁻¹) * (j * S.z * j⁻¹) := hββ x
      _ = i * S.z * i⁻¹ * (j * S.z * j⁻¹) := by rw [hi]
      _ = j * S.z * j⁻¹ * (i * S.z * i⁻¹) := hc _ hiA
      _ = q * (j * S.z * j⁻¹) * q⁻¹ := hqβ.symm
      _ = q * j * S.z * (q * j)⁻¹ := by group
  · have key : ∀ x ∈ B, A ≤ S.Qa i → j * S.z * j⁻¹ ∈ S.Qa i → x ∈ S.Qa i :=
      fun x hx hAi hβi => by
        rcases hB x hx with h | h
        · exact hAi h
        · rw [hββ x]
          exact (S.Qa i).mul_mem (hAi h) hβi
    by_cases hcA : i * S.z * i⁻¹ ∈ A
    · exact fun x hx => key x hx (hA.le_Qa i hcA) (hall i hcA)
    have h := (hB _ hi).resolve_left hcA
    have hAc : A ≤ S.Qa i := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]
        exact one_mem _
      obtain ⟨l, rfl⟩ := hA.conj v hv hv1
      have hcv : i * S.z * i⁻¹ ∈ S.Qa l := by
        rw [hββ (i * S.z * i⁻¹)]
        exact (S.Qa l).mul_mem (hA.le_Qa l hv h) (hall l hv)
      exact S.mem_Qa_symm (fun e => hcA (by rw [e]; exact hv)) hcv
    refine fun x hx => key x hx hAc ?_
    have e : j * S.z * j⁻¹ = (i * S.z * i⁻¹)⁻¹ * (i * S.z * i⁻¹ * (j * S.z * j⁻¹)) := by group
    rw [e]
    exact (S.Qa i).mul_mem ((S.Qa i).inv_mem (S.conj_z_mem_Qa i)) (hAc h)

theorem Cfg111.star (C : Cfg111 S g A) {k j : G} (hk : k * S.z * k⁻¹ ∈ A)
    (hkz : k * S.z * k⁻¹ ≠ S.z) (hjQ : j * S.z * j⁻¹ ∈ S.QG) (hjk : j * S.z * j⁻¹ ∈ S.Qa k) :
    j * S.z * j⁻¹ ∈ A := by
  by_contra hjA
  by_cases hall : ∀ i : G, i * S.z * i⁻¹ ∈ A → j * S.z * j⁻¹ ∈ S.Qa i
  · obtain ⟨B, hB, hAB, hjB⟩ := C.inc.exists_adjoin hjQ hjA hall
    have hAB' := Subgroup.eq_of_le_of_card_ge hAB (C.max B hB (hAB C.mem))
    exact hjA (hAB' ▸ hjB)
  · push Not at hall
    obtain ⟨i, hi, hji⟩ := hall
    exact C.not111 (C.inc.two_point C.hy hk hkz hi hjQ hjk hji)

theorem Cfg111.map_eq_of_conj_mem (C : Cfg111 S g A) {h k : G} (hh : h ∈ S.M)
    (hk : k * S.z * k⁻¹ ∈ A) (hkz : k * S.z * k⁻¹ ≠ S.z) (hhk : h * (k * S.z * k⁻¹) * h⁻¹ ∈ A) :
    A.map (MulAut.conj h).toMonoidHom = A := by
  have hhkz : (h * k) * S.z * (h * k)⁻¹ ≠ S.z := conj_ne_z' S hh hkz
  have hhk' : (h * k) * S.z * (h * k)⁻¹ ∈ A := by
    rw [mul_conj_z S]
    exact hhk
  have hle : A.map (MulAut.conj h).toMonoidHom ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hx1 : x = 1
    · rw [hx1, map_one]
      exact one_mem _
    obtain ⟨j, rfl⟩ := C.inc.conj x hx hx1
    have e : (MulAut.conj h).toMonoidHom (j * S.z * j⁻¹) = (h * j) * S.z * (h * j)⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    refine C.star hhk' hhkz (conj_mem_QG' S hh (C.inc.le_QG hx)) ?_
    rw [mul_conj_z S]
    exact conj_mem_Qa_mul S (C.inc.le_Qa k hk hx)
  exact Subgroup.eq_of_le_of_card_ge hle (card_map_conj A h).ge

theorem Cfg111.inter (C : Cfg111 S g A) {h : G} (hh : h ∈ S.M) :
    A.map (MulAut.conj h).toMonoidHom = A ∨
      A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z := by
  by_cases hex : ∃ x ∈ A ⊓ A.map (MulAut.conj h).toMonoidHom, x ≠ 1 ∧ x ≠ S.z
  · obtain ⟨x, hx, hx1, hxz⟩ := hex
    obtain ⟨hxA, hxh⟩ := Subgroup.mem_inf.mp hx
    rw [mem_map_conj_iff] at hxh
    have hxe : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    have hy1 : h⁻¹ * x * h ≠ 1 := fun e => hx1 (by rw [hxe, e]; group)
    obtain ⟨k, hk⟩ := C.inc.conj _ hxh hy1
    have hkA : k * S.z * k⁻¹ ∈ A := hk ▸ hxh
    have hkz : k * S.z * k⁻¹ ≠ S.z := fun e => hxz (by
      rw [hxe, hk, e, S.z_comm hh, mul_inv_cancel_right])
    refine Or.inl (C.map_eq_of_conj_mem hh hkA hkz ?_)
    rw [← hk, ← hxe]
    exact hxA
  · refine Or.inr (le_antisymm (fun x hx => ?_) ?_)
    · push Not at hex
      rw [Setting.mem_zpowers_iff_of_mul_self S.z_mul_z]
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hex x hx hx1)
    · rw [zpowers_le]
      exact ⟨C.inc.z_mem, (C.inc.map_conj hh).z_mem⟩

theorem Cfg111.map_eq_of_mem_normalizer (C : Cfg111 S g A) {m : S.M}
    (hm : S.ρ m ∈ normalizer (S.Lbar g : Set S.O)) :
    A.map (MulAut.conj (m : G)).toMonoidHom = A := by
  have H := C.hy.hyp4
  have h1 := fix_of_mem_normalizer H hm
  rw [ρ_cl_conj_z S m H.conj_mem] at h1
  apply C.map_eq_of_conj_mem m.2 C.mem H.conj_ne
  rcases (S.cl_eq_cl_iff (conj_mem_QG' S m.2 H.conj_mem) H.conj_mem).mp h1 with e | e
  · rw [← mul_conj_z S, ← e]
    exact C.mem
  · have e' : (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ = g * S.z * g⁻¹ * S.z := by
      calc (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹
          = (m : G) * g * S.z * ((m : G) * g)⁻¹ * (S.z * S.z) := by
            rw [S.z_mul_z]
            group
        _ = g * S.z * g⁻¹ * S.z := by
            rw [e]
            group
    rw [e']
    exact A.mul_mem C.mem C.inc.z_mem

theorem Cfg111.mem_of_Lbar_inf_ne_bot (C : Cfg111 S g A) {k j : G} (hk : k * S.z * k⁻¹ ∈ A)
    (hkz : k * S.z * k⁻¹ ≠ S.z) (hjQ : j * S.z * j⁻¹ ∈ S.QG) (hjz : j * S.z * j⁻¹ ≠ S.z)
    (hne : S.Lbar k ⊓ S.Lbar j ≠ ⊥) : j * S.z * j⁻¹ ∈ A := by
  obtain ⟨⟨s, hsk, hsj⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨y, hyL, rfl⟩ := (mem_Lbar S).mp hsk
  obtain ⟨y', hy'L, hyy⟩ := (mem_Lbar S).mp hsj
  have hyQ : (y : G) ∉ S.QG := fun h => hs1 (Subtype.ext ((S.ρ_eq_one_iff y).mpr h))
  have hyj : (y : G) ∈ S.La j := by
    have hq : ((y'⁻¹ * y : S.M) : G) ∈ S.QG := by
      rw [← S.ρ_eq_one_iff (y'⁻¹ * y), map_mul, map_inv, hyy, inv_mul_cancel]
    have := mul_mem ((L0_le_La S j) hy'L) ((QG_le_La S j) hq)
    simpa using this
  exact C.star hk hkz hjQ (C.hy.mem_Qa_of_mem_La (C.inc.le_QG hk) hkz hyL hyQ hjQ hjz hyj)

end CFSG.LargeExtraspecial.S11

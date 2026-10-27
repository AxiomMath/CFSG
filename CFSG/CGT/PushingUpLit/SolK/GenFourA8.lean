module

public import CFSG.GH74.SectionalRank
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.GH74 Matrix

section Greedy

variable {X : Type*} [Group X] [Finite X]

theorem two_mul_card_le_of_lt' {A B : Subgroup X} (h : A < B) : 2 * Nat.card A ≤ Nat.card B := by
  have hd : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le h.le
  obtain ⟨c, hc⟩ := hd
  have hlt : Nat.card A < Nat.card B := Subgroup.card_lt_of_lt h
  have hpos : 0 < Nat.card A := Nat.card_pos
  rcases c with _ | _ | c
  · simp at hc
    omega
  · simp at hc
    omega
  · rw [hc]
    nlinarith

theorem exists_gen_of_start (P : Subgroup X) (s₀ : Finset X) (hs₀ : (s₀ : Set X) ⊆ P) (e : ℕ)
    (h₀ : 2 ^ (s₀.card + e) ≤ Nat.card (Subgroup.closure (s₀ : Set X))) :
    ∃ t : Finset X, (t : Set X) ⊆ P ∧ Subgroup.closure (t : Set X) = P ∧
      2 ^ (t.card + e) ≤ Nat.card P := by
  classical
  have key : ∀ (n : ℕ) (s : Finset X), Nat.card P - Nat.card (Subgroup.closure (s : Set X)) = n →
      (s : Set X) ⊆ P → 2 ^ (s.card + e) ≤ Nat.card (Subgroup.closure (s : Set X)) →
      ∃ t : Finset X, (t : Set X) ⊆ P ∧ Subgroup.closure (t : Set X) = P ∧
        2 ^ (t.card + e) ≤ Nat.card P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hn hsP hs
      by_cases hP : Subgroup.closure (s : Set X) = P
      · exact ⟨s, hsP, hP, by simpa [hP] using hs⟩
      · have hle : Subgroup.closure (s : Set X) ≤ P := (Subgroup.closure_le P).2 hsP
        have hlt : Subgroup.closure (s : Set X) < P := lt_of_le_of_ne hle hP
        obtain ⟨g, hgP, hgs⟩ := IsConcreteLE.exists_of_lt hlt
        have hgs' : g ∉ Subgroup.closure (s : Set X) := hgs
        have hgnot : g ∉ s := fun h => hgs' (Subgroup.subset_closure h)
        have hsub : (insert g s : Finset X).card = s.card + 1 := Finset.card_insert_of_notMem hgnot
        have hlt1 : Subgroup.closure (s : Set X) <
            Subgroup.closure ((insert g s : Finset X) : Set X) := by
          refine lt_of_le_of_ne ?_ ?_
          · exact Subgroup.closure_mono (by simp)
          · intro heq
            apply hgs'
            rw [heq]
            exact Subgroup.subset_closure (by simp)
        have h2 := two_mul_card_le_of_lt' hlt1
        have hsub' : ((insert g s : Finset X) : Set X) ⊆ P := by
          intro y hy
          rw [Finset.coe_insert] at hy
          rcases hy with rfl | hy
          · exact hgP
          · exact hsP hy
        have hle1 : Subgroup.closure ((insert g s : Finset X) : Set X) ≤ P :=
          (Subgroup.closure_le P).2 hsub'
        have hcardle : Nat.card (Subgroup.closure ((insert g s : Finset X) : Set X)) ≤
            Nat.card P := Subgroup.card_le_of_le hle1
        have hltcard : Nat.card (Subgroup.closure (s : Set X)) <
            Nat.card (Subgroup.closure ((insert g s : Finset X) : Set X)) :=
          Subgroup.card_lt_of_lt hlt1
        refine ih (Nat.card P - Nat.card (Subgroup.closure ((insert g s : Finset X) : Set X)))
          ?_ _ rfl hsub' ?_
        · omega
        · rw [hsub, Nat.add_right_comm, pow_succ]
          omega
  exact key _ s₀ rfl hs₀ h₀

theorem sectionalTwoRankLE_four_of_data {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 64)
    (hsq : Nat.card {x : V // x * x = 1} ≤ 31)
    (hgen : ∃ s : Finset V, s.card ≤ 4 ∧ Subgroup.closure (s : Set V) = ⊤) :
    SectionalTwoRankLE V 4 := by
  classical
  intro P hP
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card P ∣ Nat.card V := Subgroup.card_subgroup_dvd_card P
  have hm6 : m ≤ 6 := by
    rw [hm, hV] at hdvd
    have : 2 ^ m ∣ 2 ^ 6 := by simpa using hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  by_cases hm4 : m ≤ 4
  · obtain ⟨t, -, ht, hcard⟩ := exists_gen_of_start P ∅ (by simp) 0 (by simp)
    refine ⟨t, ?_, ht⟩
    rw [hm] at hcard
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (by simpa using hcard)
    omega
  · by_cases hm5 : m = 5
    · subst hm5
      have hP32 : Nat.card P = 32 := by rw [hm]; norm_num
      obtain ⟨x, hxP, hx2⟩ : ∃ x ∈ P, x * x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have := Nat.card_le_card_of_injective
          (fun x : P => (⟨(x : V), hcon x x.2⟩ : {x : V // x * x = 1}))
          (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
        omega
      have hord : orderOf x ∣ 2 ^ 5 := by
        have : orderOf x ∣ Nat.card P := by
          have := orderOf_dvd_natCard (⟨x, hxP⟩ : P)
          rwa [Subgroup.orderOf_mk] at this
        rw [hP32] at this
        norm_num
        exact this
      have hx4 : 4 ≤ orderOf x := by
        obtain ⟨k, hk, hkx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
        by_contra hlt
        have hk1 : k ≤ 1 := by
          by_contra hk2
          have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hx2' : x ^ 2 = 1 := by
          have : orderOf x ∣ 2 := by
            rw [hkx]
            interval_cases k <;> simp
          exact orderOf_dvd_iff_pow_eq_one.1 this
        exact hx2 (by rw [← pow_two]; exact hx2')
      have h4 : 2 ^ (1 + 1) ≤ Nat.card (Subgroup.closure (({x} : Finset V) : Set V)) := by
        rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
        simpa using hx4
      obtain ⟨t, -, ht, hcard⟩ := exists_gen_of_start P {x} (by simpa using hxP) 1 h4
      refine ⟨t, ?_, ht⟩
      rw [hP32] at hcard
      have : 2 ^ (t.card + 1) ≤ 2 ^ 5 := by simpa using hcard
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
      omega
    · have hm6' : m = 6 := by omega
      subst hm6'
      have hPtop : P = ⊤ := Subgroup.eq_top_of_card_eq P (by rw [hm, hV]; norm_num)
      obtain ⟨s, hs, hsP⟩ := hgen
      exact ⟨s, hs, by rw [hsP, hPtop]⟩

theorem SectionalTwoRankLE.of_sylow (S : Sylow 2 X) {r : ℕ}
    (h : SectionalTwoRankLE (S : Subgroup X) r) : SectionalTwoRankLE X r := by
  classical
  intro P hP
  obtain ⟨S', hPS'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S S'
  have hSS' : (S' : Subgroup X) = (S : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  let e : (S : Subgroup X) ≃* (S' : Subgroup X) :=
    (MulAut.conj g).subgroupMap (S : Subgroup X) |>.trans (MulEquiv.subgroupCongr hSS'.symm)
  have hS' : SectionalTwoRankLE (S' : Subgroup X) r := SectionalTwoRankLE.of_mulEquiv e h
  have hPP : IsPGroup 2 ↥(P.subgroupOf (S' : Subgroup X)) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPS').symm
  obtain ⟨s, hs, hsP⟩ := hS' _ hPP
  refine ⟨s.image (S' : Subgroup X).subtype, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsP, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hPS']

end Greedy

section Unitriangular

@[expose] def uMat (n : Fin 6 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, n 0, n 1, n 2; 0, 1, n 3, n 4; 0, 0, 1, n 5; 0, 0, 0, 1]

@[expose] def uMul (a b : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![a 0 + b 0, a 1 + b 1 + a 0 * b 3, a 2 + b 2 + a 0 * b 4 + a 1 * b 5, a 3 + b 3,
    a 4 + b 4 + a 3 * b 5, a 5 + b 5]

@[expose] def uInv (a : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![a 0, a 1 + a 0 * a 3, a 2 + a 0 * (a 4 + a 3 * a 5) + a 1 * a 5, a 3, a 4 + a 3 * a 5, a 5]

theorem uMat_mul (a b : Fin 6 → ZMod 2) : uMat a * uMat b = uMat (uMul a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, uMul, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uMat_zero : uMat 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMul_uInv (a : Fin 6 → ZMod 2) : uMul a (uInv a) = 0 := by
  revert a
  decide

theorem uMul_uInv' (a : Fin 6 → ZMod 2) : uMul (uInv a) a = 0 := by
  revert a
  decide

theorem uMat_injective : Function.Injective uMat := by
  intro a b h
  funext i
  fin_cases i
  · exact congrFun (congrFun h 0) 1
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 0) 3
  · exact congrFun (congrFun h 1) 2
  · exact congrFun (congrFun h 1) 3
  · exact congrFun (congrFun h 2) 3

@[expose] def gMat (n : Fin 6 → ZMod 2) : GL (Fin 4) (ZMod 2) where
  val := uMat n
  inv := uMat (uInv n)
  val_inv := by rw [uMat_mul, uMul_uInv, uMat_zero]
  inv_val := by rw [uMat_mul, uMul_uInv', uMat_zero]

theorem gMat_injective : Function.Injective gMat := fun _ _ h =>
  uMat_injective (congrArg Units.val h)

theorem gMat_mul (a b : Fin 6 → ZMod 2) : gMat a * gMat b = gMat (uMul a b) :=
  Units.ext (uMat_mul a b)

@[expose] def uSub : Subgroup (GL (Fin 4) (ZMod 2)) where
  carrier := Set.range gMat
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨uMul a b, (gMat_mul a b).symm⟩
  one_mem' := ⟨0, Units.ext uMat_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨uInv a, Units.ext rfl⟩

end Unitriangular

section SylowTwo

theorem card_uSub : Nat.card ↥uSub = 64 := by
  have h : Nat.card (Set.range gMat) = Nat.card (Fin 6 → ZMod 2) :=
    Nat.card_range_of_injective gMat_injective
  change Nat.card (Set.range gMat) = 64
  rw [h, Nat.card_eq_fintype_card]
  simp [ZMod.card]

@[expose] def gS (n : Fin 6 → ZMod 2) : ↥uSub := ⟨gMat n, n, rfl⟩

theorem gS_mul (a b : Fin 6 → ZMod 2) : gS a * gS b = gS (uMul a b) := Subtype.ext (gMat_mul a b)

theorem gS_zero : gS 0 = 1 := Subtype.ext (Units.ext uMat_zero)

theorem gS_inv (a : Fin 6 → ZMod 2) : (gS a)⁻¹ = gS (uInv a) :=
  inv_eq_of_mul_eq_one_right (by rw [gS_mul, uMul_uInv, gS_zero])

theorem gS_injective : Function.Injective gS := fun _ _ h =>
  gMat_injective (congrArg Subtype.val h)

theorem card_sq_params : Nat.card {n : Fin 6 → ZMod 2 // uMul n n = 0} = 28 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem sq_params_of {n : Fin 6 → ZMod 2} (h : gS n * gS n = 1) : uMul n n = 0 := by
  rw [gS_mul, ← gS_zero] at h
  exact gS_injective h

theorem card_sq_uSub : Nat.card {x : ↥uSub // x * x = 1} ≤ 31 := by
  have hn : ∀ x : {x : ↥uSub // x * x = 1}, ∃ n, gS n = x.1 := fun x => by
    obtain ⟨n, hn⟩ := x.1.2
    exact ⟨n, Subtype.ext hn⟩
  let f : {x : ↥uSub // x * x = 1} → {n : Fin 6 → ZMod 2 // uMul n n = 0} := fun x =>
    ⟨(hn x).choose, sq_params_of (by rw [(hn x).choose_spec]; exact x.2)⟩
  have hf : Function.Injective f := by
    intro x y h
    have h1 : (hn x).choose = (hn y).choose := congrArg Subtype.val h
    exact Subtype.ext (by rw [← (hn x).choose_spec, ← (hn y).choose_spec, h1])
  have h2 := Nat.card_le_card_of_injective f hf
  have h3 := card_sq_params
  omega

@[expose] def rt (i : Fin 6) (b : ZMod 2) : Fin 6 → ZMod 2 := Pi.single i b

theorem uMul_decomp (n : Fin 6 → ZMod 2) :
    uMul (uMul (uMul (uMul (uMul (rt 2 (n 2)) (rt 4 (n 4))) (rt 5 (n 5))) (rt 3 (n 3)))
      (rt 1 (n 1))) (rt 0 (n 0)) = n := by
  revert n
  decide

theorem comm_e1 :
    uMul (uMul (uMul (rt 0 1) (rt 3 1)) (uInv (rt 0 1))) (uInv (rt 3 1)) = rt 1 1 := by
  decide

theorem comm_e4 :
    uMul (uMul (uMul (rt 3 1) (rt 5 1)) (uInv (rt 3 1))) (uInv (rt 5 1)) = rt 4 1 := by
  decide

theorem comm_e2 :
    uMul (uMul (uMul (rt 1 1) (rt 5 1)) (uInv (rt 1 1))) (uInv (rt 5 1)) = rt 2 1 := by
  decide

theorem closure_gS :
    Subgroup.closure ({gS (rt 0 1), gS (rt 3 1), gS (rt 5 1)} : Set ↥uSub) = ⊤ := by
  set C : Subgroup ↥uSub := Subgroup.closure ({gS (rt 0 1), gS (rt 3 1), gS (rt 5 1)} : Set ↥uSub)
    with hC
  have h0 : gS (rt 0 1) ∈ C := Subgroup.subset_closure (by simp)
  have h3 : gS (rt 3 1) ∈ C := Subgroup.subset_closure (by simp)
  have h5 : gS (rt 5 1) ∈ C := Subgroup.subset_closure (by simp)
  have hcomm : ∀ a b c : Fin 6 → ZMod 2, gS a ∈ C → gS b ∈ C → uMul (uMul (uMul a b) (uInv a))
      (uInv b) = c → gS c ∈ C := by
    intro a b c ha hb habc
    rw [← habc, ← gS_mul, ← gS_mul, ← gS_mul, ← gS_inv, ← gS_inv]
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)
  have h1 : gS (rt 1 1) ∈ C := hcomm _ _ _ h0 h3 comm_e1
  have h4 : gS (rt 4 1) ∈ C := hcomm _ _ _ h3 h5 comm_e4
  have h2 : gS (rt 2 1) ∈ C := hcomm _ _ _ h1 h5 comm_e2
  have hroot : ∀ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) := by decide
  have hrt : ∀ (i : Fin 6) (b : ZMod 2), gS (rt i b) ∈ C := by
    intro i b
    have hb : b = 0 ∨ b = 1 := by revert b; decide
    rcases hb with rfl | rfl
    · have : rt i 0 = 0 := by simp [rt]
      rw [this, gS_zero]
      exact C.one_mem
    · rcases hroot i with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn⟩ := x.2
  have hx : x = gS n := Subtype.ext hn.symm
  rw [hx, ← uMul_decomp n, ← gS_mul, ← gS_mul, ← gS_mul, ← gS_mul, ← gS_mul]
  exact C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (hrt _ _) (hrt _ _)) (hrt _ _))
    (hrt _ _)) (hrt _ _)) (hrt _ _)

theorem sectionalTwoRankLE_uSub : SectionalTwoRankLE ↥uSub 4 := by
  refine sectionalTwoRankLE_four_of_data card_uSub card_sq_uSub ?_
  refine ⟨{gS (rt 0 1), gS (rt 3 1), gS (rt 5 1)}, ?_, ?_⟩
  · exact (Finset.card_le_three).trans (by norm_num)
  · rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
    exact closure_gS

noncomputable def uSylow : Sylow 2 (GL (Fin 4) (ZMod 2)) :=
  IsPGroup.toSylow (P := uSub) (IsPGroup.of_card (n := 6) (by rw [card_uSub]; norm_num)) (by
    have h := Subgroup.card_mul_index uSub
    rw [card_uSub, CFSG.GH74.Exceptional.card_GL_four_two] at h
    have : uSub.index = 315 := by omega
    rw [this]
    norm_num)

theorem sectionalTwoRankLE_GL_four_two : SectionalTwoRankLE (GL (Fin 4) (ZMod 2)) 4 :=
  SectionalTwoRankLE.of_sylow uSylow sectionalTwoRankLE_uSub

end SylowTwo

end CFSG.CGT.PushingUpLit.SolK

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerS3Main

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

structure OverGroup (G Fn N : Subgroup (V ≃ₗ[k] V)) : Prop where
  le_G : Fn ≤ G
  normal : (Fn.subgroupOf G).Normal
  odd : Odd (Nat.card Fn)
  N_le : N ≤ Fn

namespace OddAbelianSetting

variable [CharP k 2] [Finite V] {G N A : Subgroup (V ≃ₗ[k] V)} {ι : Type*}
  {g : ι → V ≃ₗ[k] V} [Fintype ι] (h : OddAbelianSetting G N A) (F : ConjFamily G N A g)

include h F

theorem sq_mem_D : ∀ b ∈ natB G N A, b ^ 2 ∈ natD N A g := by
  have hder : ∀ x ∈ natB G N A, ∀ y ∈ natB G N A, ⁅x, y⁆ ∈ natD N A g := by
    intro x hx y hy
    have := Subgroup.commutator_mem_commutator hx hy
    rwa [h.B_derived F] at this
  have hDnorm : ∀ x ∈ G, ∀ d ∈ natD N A g, x * d * x⁻¹ ∈ natD N A g := fun x hx d hd =>
    (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer ((h.D_le_N F).trans h.N_le)).1
        (h.D_normal F) hx) d).1 hd
  have key : ∀ b ∈ (⨆ i, natS N A g i : Subgroup (V ≃ₗ[k] V)),
      b ∈ natB G N A ∧ b ^ 2 ∈ natD N A g := by
    intro b hb
    refine Subgroup.iSup_induction (natS N A g) hb
      (C := fun b => b ∈ natB G N A ∧ b ^ 2 ∈ natD N A g) ?_ ?_ ?_
    · intro j x hx
      refine ⟨h.S_le_B F j hx, ?_⟩
      have pd := h.planeData_family F j
      obtain ⟨l, hl, a, ha, rfl⟩ := mem_sup_mul pd.A_norm hx
      have ha2 : a ^ 2 = 1 := by
        have := pow_card_eq_one' (G := ↥(natA A g j)) (x := ⟨a, ha⟩)
        rw [pd.card_A] at this
        exact congrArg Subtype.val this
      have e : (l * a) ^ 2 = l * (a * l * a⁻¹) := by
        calc (l * a) ^ 2 = l * (a * l * a⁻¹) * (a * a) := by rw [pow_two]; group
          _ = l * (a * l * a⁻¹) * a ^ 2 := by rw [pow_two]
          _ = l * (a * l * a⁻¹) := by rw [ha2, mul_one]
      rw [e]
      have h1 : a * l * a⁻¹ ∈ natL N A g j := (Subgroup.mem_normalizer_iff.1 (pd.A_norm ha) l).1 hl
      exact le_iSup (natL N A g) j ((natL N A g j).mul_mem hl h1)
    · exact ⟨Subgroup.one_mem _, by simp⟩
    · rintro x y ⟨hxB, hx2⟩ ⟨hyB, hy2⟩
      refine ⟨Subgroup.mul_mem _ hxB hyB, ?_⟩
      have hxG : x ∈ G := h.natB_le hxB
      have e : (x * y) ^ 2 = (x * ⁅y, x⁆ * x⁻¹) * x ^ 2 * y ^ 2 := by
        simp only [commutatorElement_def, pow_two]
        group
      rw [e]
      exact (natD N A g).mul_mem ((natD N A g).mul_mem (hDnorm x hxG _ (hder y hyB x hxB)) hx2) hy2
  intro b hb
  rw [h.B_eq F] at hb
  exact (key b hb).2

theorem odd_mem_D {Fn : Subgroup (V ≃ₗ[k] V)} (hodd : Odd (Nat.card Fn)) {u : V ≃ₗ[k] V}
    (hu : u ∈ natB G N A) (huF : u ∈ Fn) : u ∈ natD N A g := by
  have hm : Odd (orderOf u) := by
    have h1 : orderOf (⟨u, huF⟩ : ↥Fn) ∣ Nat.card Fn := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  obtain ⟨t, ht⟩ := hm
  have h1 : u ^ (orderOf u) = 1 := pow_orderOf_eq_one u
  have h2 : u = (u ^ 2) ^ (t + 1) := by
    calc u = u ^ (orderOf u + 1) := by rw [pow_succ, h1, one_mul]
      _ = (u ^ 2) ^ (t + 1) := by rw [← pow_mul]; congr 1; omega
  rw [h2]
  exact Subgroup.pow_mem _ (h.sq_mem_D F u hu) (t + 1)

theorem D_act (i : ι) :
    ∀ d ∈ natD N A g, ∃ l ∈ natL N A g i, ∀ w ∈ natI N A g i, d w = l w := by
  have fd := h.famData F
  obtain ⟨hW, -⟩ := h.S_action F i
  intro d hd
  refine Subgroup.iSup_induction (natL N A g) hd
    (C := fun d => ∃ l ∈ natL N A g i, ∀ w ∈ natI N A g i, d w = l w) ?_ ?_ ?_
  · intro j x hx
    by_cases hji : j = i
    · subst hji
      exact ⟨x, hx, fun w _ => rfl⟩
    · exact ⟨1, Subgroup.one_mem _, fun w hw => by rw [fd.L_fix_I j i hji x hx w hw]; rfl⟩
  · exact ⟨1, Subgroup.one_mem _, fun w _ => rfl⟩
  · rintro x y ⟨l, hl, hxl⟩ ⟨l', hl', hyl⟩
    refine ⟨l * l', (natL N A g i).mul_mem hl hl', fun w hw => ?_⟩
    have hl'w : l' w ∈ natI N A g i :=
      hW l' ((le_sup_left : natL N A g i ≤ natS N A g i) hl') w hw
    show x (y w) = l (l' w)
    rw [hyl w hw, hxl _ hl'w]

omit [Fintype ι] in
theorem S_ext (i : ι) {y z : V ≃ₗ[k] V} (hy : y ∈ natS N A g i) (hz : z ∈ natS N A g i)
    (hyz : ∀ w ∈ natI N A g i, y w = z w) : y = z := by
  obtain ⟨hW, hbij⟩ := h.S_action F i
  have : (⟨y, hy⟩ : ↥(natS N A g i)) = ⟨z, hz⟩ := by
    apply hbij.1
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [resSub_apply, resSub_apply]
    exact hyz w w.2
  exact congrArg Subtype.val this

omit [Fintype ι] in
theorem exists_ne_one_A (i : ι) : ∃ a ∈ natA A g i, a ≠ 1 := by
  have pd := h.planeData_family F i
  by_contra hcon
  have : natA A g i = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun a ha => by
    by_contra h1
    exact hcon ⟨a, ha, h1⟩
  have h2 := pd.card_A
  rw [this, Subgroup.card_bot] at h2
  omega

omit [Fintype ι] in
theorem not_centralizes_A (i : ι) {a : V ≃ₗ[k] V} (ha : a ∈ natA A g i) (ha1 : a ≠ 1) :
    ¬ ∀ x ∈ natL N A g i, a * x = x * a := by
  intro hc
  have pd := h.planeData_family F i
  have hA2 : Nat.card (natA A g i) = 2 := pd.card_A
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : ⁅natL N A g i, natA A g i⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx b hb
    have hz := mem_zpowers_of_prime_card (g := (⟨a, ha⟩ : ↥(natA A g i))) hA2
      (fun e => ha1 (congrArg Subtype.val e)) (g' := ⟨b, hb⟩)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hbn : a ^ n = b := by simpa using congrArg Subtype.val hn
    have hcx : Commute a x := hc x hx
    have hbx : Commute b x := by
      rw [← hbn]
      exact hcx.zpow_left n
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 hbx.symm.eq
  rw [pd.L_perf] at hbot
  have h3 : Nat.card (natL N A g i) = 1 := by rw [hbot]; exact Subgroup.card_bot
  have := pd.card_L
  omega

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer

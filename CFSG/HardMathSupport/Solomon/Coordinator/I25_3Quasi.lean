module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Quasi

variable {N T : Type*} [Group N] [Group T]

theorem i253_comm_mul_central {a b z z' : N} (hz : z ∈ Subgroup.center N)
    (hz' : z' ∈ Subgroup.center N) : ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  have zc : ∀ g : N, g * z = z * g := Subgroup.mem_center_iff.1 hz
  have zc' : ∀ g : N, g * z' = z' * g := Subgroup.mem_center_iff.1 hz'
  have s1 : z * (b * z') * z⁻¹ = b * z' := by rw [← zc (b * z'), mul_inv_cancel_right]
  have s2 : z' * a⁻¹ * z'⁻¹ = a⁻¹ := by rw [← zc' a⁻¹, mul_inv_cancel_right]
  calc ⁅a * z, b * z'⁆ = a * (z * (b * z') * z⁻¹) * a⁻¹ * (z'⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = a * b * (z' * a⁻¹ * z'⁻¹) * b⁻¹ := by rw [s1]; group
    _ = ⁅a, b⁆ := by rw [s2]; simp [commutatorElement_def, mul_assoc]

theorem i253_normal_le_center_or_top (hq : CFSG.Open.IsQuasisimple N) (M : Subgroup N) [M.Normal] :
    M ≤ Subgroup.center N ∨ M = ⊤ := by
  have hs := hq.2
  have hnorm : (M.map (QuotientGroup.mk' (Subgroup.center N))).Normal :=
    Subgroup.Normal.map (inferInstance : M.Normal) _ (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center N))) with h | h
  · left
    intro x hx
    have : QuotientGroup.mk' (Subgroup.center N) x ∈ M.map (QuotientGroup.mk' (Subgroup.center N)) :=
      ⟨x, hx, rfl⟩
    rw [h] at this
    exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 this)
  · right
    have hcomm : ∀ a b : N, ⁅a, b⁆ ∈ M := by
      intro a b
      have ha : QuotientGroup.mk' (Subgroup.center N) a ∈
          M.map (QuotientGroup.mk' (Subgroup.center N)) := by rw [h]; trivial
      have hb : QuotientGroup.mk' (Subgroup.center N) b ∈
          M.map (QuotientGroup.mk' (Subgroup.center N)) := by rw [h]; trivial
      obtain ⟨m, hm, hma⟩ := ha
      obtain ⟨m', hm', hmb⟩ := hb
      have hza : m⁻¹ * a ∈ Subgroup.center N := QuotientGroup.eq.1 hma
      have hzb : m'⁻¹ * b ∈ Subgroup.center N := QuotientGroup.eq.1 hmb
      have ea : a = m * (m⁻¹ * a) := by group
      have eb : b = m' * (m'⁻¹ * b) := by group
      rw [ea, eb, i253_comm_mul_central hza hzb]
      simp only [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')
    have hc : ⁅(⊤ : Subgroup N), ⊤⁆ ≤ M := Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
    have h1 := hq.1
    rw [commutator_def] at h1
    rw [eq_top_iff, ← h1]
    exact hc

theorem i253_isQuasisimple_of_surj (hq : CFSG.Open.IsQuasisimple N) (f : N →* T)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center N) :
    CFSG.Open.IsQuasisimple T := by
  have hperf : Group.IsPerfect N := Group.isPerfect_def.2 hq.1
  refine ⟨?_, ?_⟩
  · have h1 := hq.1
    rw [commutator_def] at h1
    have h2 := Subgroup.map_commutator ⊤ ⊤ f
    rw [h1, Subgroup.map_top_of_surjective f hf] at h2
    rw [commutator_def]
    exact h2.symm
  · have hZ : ∀ z ∈ Subgroup.center T, ∃ n ∈ Subgroup.center N, f n = z := by
      intro z hz
      obtain ⟨n, rfl⟩ := hf z
      refine ⟨n, ?_, rfl⟩
      have hc := Group.IsPerfect.center_quotient_center_eq_bot N
      have : (QuotientGroup.mk n : N ⧸ Subgroup.center N) ∈
          Subgroup.center (N ⧸ Subgroup.center N) := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hcomm : f (m * n) = f (n * m) := by
          rw [map_mul, map_mul]
          exact Subgroup.mem_center_iff.1 hz (f m)
        have hk : (m * n)⁻¹ * (n * m) ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hcomm, inv_mul_cancel]
        exact hker hk
      rw [hc] at this
      exact (QuotientGroup.eq_one_iff n).1 (Subgroup.mem_bot.1 this)
    let g : N →* T ⧸ Subgroup.center T := (QuotientGroup.mk' _).comp f
    have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
    have hgker : g.ker = Subgroup.center N := by
      ext x
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk (f x) : T ⧸ Subgroup.center T) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff]
      constructor
      · intro hx
        obtain ⟨n, hn, hfn⟩ := hZ _ hx
        have : x⁻¹ * n ∈ f.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hfn, inv_mul_cancel]
        have h3 := (Subgroup.center N).mul_mem hn ((Subgroup.center N).inv_mem (hker this))
        have h4 : n * (x⁻¹ * n)⁻¹ = x := by group
        rwa [h4] at h3
      · intro hx
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro t
        obtain ⟨y, rfl⟩ := hf t
        rw [← map_mul, ← map_mul, hx y]
    have e : (N ⧸ Subgroup.center N) ≃* (T ⧸ Subgroup.center T) :=
      (QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective g hg)
    have : IsSimpleGroup (N ⧸ Subgroup.center N) := hq.2
    exact e.symm.isSimpleGroup

end Quasi

section Component

variable {G : Type*} [Group G] [Finite G]

theorem i253_glaPComponent_of_subnormal {X S : Subgroup G} (hSX : S ≤ X) (hsn : IsSubnormal S X)
    (hq : CFSG.Open.IsQuasisimple ↥S) (h3 : 3 ∣ Nat.card S) : GLAPComponent 3 X S := by
  classical
  let O : Subgroup ↥X := GLAPPrimeCore 3 ↥X
  let Lb : Subgroup ↥X := S.subgroupOf X
  let π : ↥X →* ↥X ⧸ O := QuotientGroup.mk' O
  let e0 : ↥Lb ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSX
  have hqL : CFSG.Open.IsQuasisimple ↥Lb :=
    i253_isQuasisimple_of_surj hq e0.symm.toMonoidHom e0.symm.surjective (by
      intro x hx
      have : x = 1 := e0.symm.injective (by simpa using hx)
      simp [this])
  have hcop : Nat.Coprime 3 (Nat.card O) := coprime_card_gLAPPrimeCore_aux 3 ↥X
  haveI : O.Normal := inferInstance
  have hNn : (O.subgroupOf Lb).Normal := Subgroup.Normal.subgroupOf inferInstance Lb
  have hN : O.subgroupOf Lb ≤ Subgroup.center ↥Lb := by
    rcases i253_normal_le_center_or_top hqL (O.subgroupOf Lb) with h | h
    · exact h
    · exfalso
      have hLbO : Lb ≤ O := fun x hx => by
        have : (⟨x, hx⟩ : ↥Lb) ∈ O.subgroupOf Lb := by rw [h]; trivial
        exact Subgroup.mem_subgroupOf.1 this
      have h3O : 3 ∣ Nat.card O :=
        (((Nat.card_congr e0.toEquiv).symm ▸ h3 : 3 ∣ Nat.card Lb)).trans
          (Subgroup.card_dvd_of_le hLbO)
      exact absurd (hcop.eq_one_of_dvd h3O) (by norm_num)
  let f' : ↥Lb →* ↥(Lb.map π) :=
    (π.comp Lb.subtype).codRestrict (Lb.map π) (fun x => ⟨x, x.2, rfl⟩)
  have hf'surj : Function.Surjective f' := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hf'ker : f'.ker ≤ Subgroup.center ↥Lb := by
    intro x hx
    apply hN
    rw [MonoidHom.mem_ker] at hx
    have h1 : π x = 1 := congrArg Subtype.val hx
    exact Subgroup.mem_subgroupOf.2 ((QuotientGroup.eq_one_iff _).1 h1)
  have hQ : CFSG.Open.IsQuasisimple ↥(Lb.map π) :=
    i253_isQuasisimple_of_surj hqL f' hf'surj hf'ker
  refine ⟨hSX, hsn, ⟨le_top, ?_, hQ⟩, ?_⟩
  · have := isSubnormal_barX (C := X) 3 hsn
    rwa [barX_self] at this
  · intro J hJS _ heq
    have heq' : (J.subgroupOf X).map π = Lb.map π := heq
    have hJL : J.subgroupOf X ≤ Lb := fun x hx => hJS.le hx
    have hdec : ∀ a : ↥Lb, ∃ j : ↥Lb, j ∈ (J.subgroupOf X).subgroupOf Lb ∧
        ∃ z ∈ Subgroup.center ↥Lb, a = j * z := by
      intro a
      have hπa : π (a : ↥X) ∈ (J.subgroupOf X).map π := by
        rw [heq']; exact ⟨a, a.2, rfl⟩
      obtain ⟨j, hj, hjπ⟩ := hπa
      have hjL : j ∈ Lb := hJL hj
      have hz : j⁻¹ * (a : ↥X) ∈ O := QuotientGroup.eq.1 hjπ
      have hzL : j⁻¹ * (a : ↥X) ∈ Lb := Lb.mul_mem (Lb.inv_mem hjL) a.2
      refine ⟨⟨j, hjL⟩, hj, ⟨j⁻¹ * (a : ↥X), hzL⟩, hN (Subgroup.mem_subgroupOf.2 hz), ?_⟩
      apply Subtype.ext
      simp
    have hcomm : ∀ a b : ↥Lb, ⁅a, b⁆ ∈ (J.subgroupOf X).subgroupOf Lb := by
      intro a b
      obtain ⟨j, hj, z, hz, rfl⟩ := hdec a
      obtain ⟨j', hj', z', hz', rfl⟩ := hdec b
      rw [i253_comm_mul_central hz hz']
      simp only [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hj hj')
        (Subgroup.inv_mem _ hj)) (Subgroup.inv_mem _ hj')
    have hc : ⁅(⊤ : Subgroup ↥Lb), ⊤⁆ ≤ (J.subgroupOf X).subgroupOf Lb :=
      Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
    have h1 := hqL.1
    rw [commutator_def] at h1
    rw [h1] at hc
    have hSJ : S ≤ J := by
      intro s hs
      have : (⟨⟨s, hSX hs⟩, hs⟩ : ↥Lb) ∈ (J.subgroupOf X).subgroupOf Lb := hc trivial
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 this)
    exact absurd hSJ (not_le_of_gt hJS)

theorem i253_central_or_eq_of_isSubnormal {K J : Subgroup G} (hsn : IsSubnormal J K) :
    CFSG.Open.IsQuasisimple ↥K →
    (∃ h : J ≤ K, ∀ x (hx : x ∈ J), (⟨x, h hx⟩ : ↥K) ∈ Subgroup.center ↥K) ∨ J = K := by
  induction hsn with
  | refl H => exact fun _ => Or.inr rfl
  | @step H M K' hHM hn hMK ih =>
    intro hK
    rcases ih hK with ⟨hMK2, hc⟩ | rfl
    · exact Or.inl ⟨hHM.trans hMK2, fun x hx => hc x (hHM hx)⟩
    · rcases i253_normal_le_center_or_top hK (H.subgroupOf M) with h | h
      · exact Or.inl ⟨hHM, fun x hx => h (Subgroup.mem_subgroupOf.2 hx)⟩
      · exact Or.inr (le_antisymm hHM (fun x hx => by
          have : (⟨x, hx⟩ : ↥M) ∈ H.subgroupOf M := by rw [h]; trivial
          exact Subgroup.mem_subgroupOf.1 this))

theorem i253_eq_of_isSubnormal {K J : Subgroup G} (hK : CFSG.Open.IsQuasisimple ↥K)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hsn : IsSubnormal J K) : J = K := by
  rcases i253_central_or_eq_of_isSubnormal hsn hK with ⟨h, hc⟩ | h
  · exfalso
    have hcomm : ∀ a b : ↥J, a * b = b * a := fun a b => by
      have := Subgroup.mem_center_iff.1 (hc a.1 a.2) ⟨b.1, h b.2⟩
      exact Subtype.ext (by simpa using congrArg Subtype.val this.symm)
    have hc2 : Subgroup.center ↥J = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      exact fun y => hcomm y x
    have := hJq.2.toNontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥J ⧸ Subgroup.center ↥J)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    apply hz
    rw [QuotientGroup.eq_one_iff, hc2]
    trivial
  · exact h

end Component

end CFSG.HardMathSupport.Solomon.Coordinator

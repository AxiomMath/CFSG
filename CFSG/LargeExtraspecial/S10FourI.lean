module

public import CFSG.LargeExtraspecial.S10FourH
public import CFSG.LargeExtraspecial.S10FourD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

@[expose] def vecStab (S : Setting G) (v : S.Qt) : Subgroup S.O where
  carrier := {x | (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  mul_mem' := fun {x y} hx hy => by
    change ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    have hx' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := hx
    have hy' : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := hy
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hy', hx']
  one_mem' := rfl
  inv_mem' := fun {x} hx => by
    change ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    have hx' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := hx
    conv_lhs => rw [← hx']
    exact inv_apply_apply_O x v

theorem mem_vecStab {v : S.Qt} {x : S.O} :
    x ∈ vecStab S v ↔ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := Iff.rfl

theorem two_mul_card_inf_vecStab {L : Subgroup S.O} {e w : S.Qt}
    (he : ∀ l ∈ L, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) e = e)
    (hw : ∀ l ∈ L, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ (ZMod 2) ∙ e) {l₀ : S.O} (hl₀ : l₀ ∈ L)
    (hl₀w : (l₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w) :
    2 * Nat.card ↥(L ⊓ vecStab S w) = Nat.card L := by
  have hcase : ∀ l ∈ L, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w ∨
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + e := by
    intro l hl
    rcases mem_span_singleton_zmod2.mp (hw l hl) with h | h
    · left; exact sub_eq_zero.mp h
    · right; rw [← h]; abel
  have h2e : e + e = 0 := ZModModule.add_self e
  have hl₀e : (l₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + e := (hcase l₀ hl₀).resolve_left hl₀w
  have he0 : e ≠ 0 := fun h0 => hl₀w (by rw [hl₀e, h0, add_zero])
  have hwe : w + e ≠ w := fun h' => he0 (by
    have := congrArg (· - w) h'
    simpa using this)
  have hindex : ((L ⊓ vecStab S w).subgroupOf L).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨l₀, hl₀⟩, fun b => ?_⟩
    have hmem : ∀ y : L, y ∈ (L ⊓ vecStab S w).subgroupOf L ↔
        ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := fun y => by
      rw [mem_subgroupOf, mem_inf, mem_vecStab]
      exact and_iff_right y.2
    rw [hmem, hmem]
    have hbl : (((b * ⟨l₀, hl₀⟩ : L) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
        ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (w + e) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
      change ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = _
      rw [hl₀e]
    rw [hbl, map_add, he b b.2]
    rcases hcase b b.2 with h | h
    · rw [h]
      simp [hwe]
    · rw [h]
      have h1 : w + e + e = w := by rw [add_assoc, h2e, add_zero]
      simp [h1, hwe]
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup ((L ⊓ vecStab S w).subgroupOf L)
  rw [← Subgroup.index_eq_card, hindex,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at this
  exact this.symm

theorem Lbar_facts (X : Hyp10 S g t) :
    (∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) ∧
    (∀ l ∈ S.Lbar g, ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g),
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) ∧
    (∀ w, w ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) →
      ∃ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w) := by
  have := Lbar_mul_facts X 1
  simpa using this

theorem mem_normalizer_of_fix' (X : Hyp10 S g t) {h : S.M} {x : S.O} (hxM : x ∈ S.Mbar)
    (hfix : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) :
    x ∈ normalizer (S.Lbar ((h : G) * g) : Set S.O) :=
  mem_normalizer_of_fix X.haQ X.H.conj_ne hxM hfix

theorem mem_normalizer_of_fix_a (X : Hyp10 S g t) {x : S.O} (hxM : x ∈ S.Mbar)
    (hfix : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) :
    x ∈ normalizer (S.Lbar g : Set S.O) := by
  have := mem_normalizer_of_fix' X (h := 1) hxM (by simpa using hfix)
  simpa using this

theorem StronglyClosedL.Lbar_le_sup (hSC : StronglyClosedL S g t) (X : Hyp10 S g t) {h : S.M}
    (hcP : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hca : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
    {x : S.O} (hxA : x ∈ S.Lbar g ⊓ Nbar S g t)
    (hxc : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) ≠
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) :
    S.Lbar g ≤ (S.Lbar g ⊓ Nbar S g t) ⊔ (S.Lbar g ⊓ S.Lbar ((h : G) * g)) := by
  have haQ := X.haQ
  obtain ⟨hfixa, htra, -⟩ := Lbar_facts X
  obtain ⟨hfixc, htrc, hmovc⟩ := Lbar_mul_facts X h
  set ea := S.cl (g * S.z * g⁻¹) with hea
  set ec := S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) with hec
  have hcQ : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S h.2 haQ
  have hca' : (h : G) * g * S.z * ((h : G) * g)⁻¹ ≠ g * S.z * g⁻¹ := fun e => hca (by
    rw [hec, e]
    exact Submodule.mem_span_singleton_self _)
  have hzQa : S.z ∈ S.Qa g := S.z_mem_Qa_of_mem_QG rfl haQ X.H.conj_ne
  have hcQa := mem_Qa_of_cl_mem' hzQa hcQ hcP
  have haQc := S.mem_Qa_symm hca' hcQa
  have haPc : ea ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := S.cl_mem_clSub ⟨haQ, haQc⟩ haQ
  have ha0 : ea ≠ 0 := cl_conj_z_ne_zero S haQ X.H.conj_ne
  have hc0 : ec ≠ 0 := cl_conj_z_ne_zero S hcQ (conj_ne_z' S h.2 X.H.conj_ne)
  have hac : ea ∉ (ZMod 2) ∙ ec := fun hmem => by
    rcases mem_span_singleton_zmod2.mp hmem with h0 | h0
    · exact ha0 h0
    · exact hca (by rw [← h0]; exact Submodule.mem_span_singleton_self _)
  have hxL : x ∈ S.Lbar g := hxA.1
  have hxM : x ∈ S.Mbar := S.Lbar_le_Mbar g hxL
  have h2 : ec + ea + ea = ec := by rw [add_assoc, ZModModule.add_self, add_zero]
  have hxc' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ec = ec + ea := by
    rcases mem_span_singleton_zmod2.mp (htra x hxL ec hcP) with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hxc
    · rw [← h0]; abel
  have hxinv : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ec = ec + ea := by
    have : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (ec + ea) = ec := by
      rw [map_add, hxc', hfixa x hxL, h2]
    conv_lhs => rw [← this]
    exact inv_apply_apply_O x _
  obtain ⟨y, hy, hya⟩ := hmovc ea hac
  have hcardK := two_mul_card_inf_vecStab hfixa (fun l hl => htra l hl ec hcP) hxL hxc
  have hcardK' := two_mul_card_inf_vecStab hfixc (fun l hl => htrc l hl ea haPc) hy hya
  have hLLc : Nat.card (S.Lbar g) = Nat.card (S.Lbar ((h : G) * g)) := by
    rw [X.C.card_Lbar, (X.C.mul h).card_Lbar]
  have hcard : Nat.card ↥(S.Lbar g ⊓ vecStab S ec) =
      Nat.card ↥(S.Lbar ((h : G) * g) ⊓ vecStab S ea) := by omega
  have hKab : ∀ a ∈ S.Lbar g ⊓ vecStab S ec, ∀ b ∈ S.Lbar g ⊓ vecStab S ec, a * b = b * a :=
    fun a ha b hb => Lbar_comm S haQ (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp hb).1
  have hZK : S.Lbar g ⊓ S.Lbar ((h : G) * g) ≤ S.Lbar g ⊓ vecStab S ec :=
    fun z hz => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1,
      hfixc z (Subgroup.mem_inf.mp hz).2⟩
  have hcomm : ∀ k ∈ S.Lbar g ⊓ vecStab S ec, ∀ k' ∈ S.Lbar ((h : G) * g) ⊓ vecStab S ea,
      k * k' * k⁻¹ * k'⁻¹ ∈ S.Lbar g ⊓ S.Lbar ((h : G) * g) := by
    intro k hk k' hk'
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨hk'1, hk'2⟩ := Subgroup.mem_inf.mp hk'
    have hkN := mem_normalizer_of_fix' X (S.Lbar_le_Mbar g hk1) hk2
    have hk'N := mem_normalizer_of_fix_a X (S.Lbar_le_Mbar _ hk'1) hk'2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : k' * k⁻¹ * k'⁻¹ ∈ S.Lbar g :=
        (mem_normalizer_iff.mp hk'N _).mp (inv_mem hk1)
      have := mul_mem hk1 h1
      rwa [show k * (k' * k⁻¹ * k'⁻¹) = k * k' * k⁻¹ * k'⁻¹ by group] at this
    · have h1 : k * k' * k⁻¹ ∈ S.Lbar ((h : G) * g) := (mem_normalizer_iff.mp hkN _).mp hk'1
      exact mul_mem h1 (inv_mem hk'1)
  have hf : ∀ z ∈ S.Lbar ((h : G) * g) ⊓ vecStab S ea,
      z * x * z⁻¹ * x⁻¹ ∈ (S.Lbar g ⊓ vecStab S ec) ⊓ (S.Lbar g ⊓ Nbar S g t) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    have hzM : z ∈ S.Mbar := S.Lbar_le_Mbar _ hz1
    have hzN := mem_normalizer_of_fix_a X hzM hz2
    have hA : z * x * z⁻¹ * x⁻¹ ∈ S.Lbar g ⊓ Nbar S g t :=
      mul_mem (hSC.conj_mem_Abar X hzM hzN hxA) (inv_mem hxA)
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hA).1, ?_⟩, hA⟩
    have hzc : (z : S.Qt ≃ₗ[ZMod 2] S.Qt) ec = ec := hfixc z hz1
    have hza : (z : S.Qt ≃ₗ[ZMod 2] S.Qt) ea = ea := hz2
    have hzinv : ((z⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (ec + ea) = ec + ea := by
      conv_lhs => rw [← hzc, ← hza, ← map_add]
      exact inv_apply_apply_O z _
    rw [mem_vecStab]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [hxinv, hzinv, map_add, hxc', hfixa x hxL, h2, hzc]
  have hJ : ∀ z ∈ S.Lbar ((h : G) * g) ⊓ vecStab S ea,
      z * x * z⁻¹ * x⁻¹ ∈ S.Lbar g ⊓ S.Lbar ((h : G) * g) →
        z ∈ S.Lbar g ⊓ S.Lbar ((h : G) * g) := by
    intro z hz hfz
    obtain ⟨hz1, -⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨?_, hz1⟩
    obtain ⟨x₀, hx₀⟩ := MonoidHom.mem_range.mp hxM
    obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar _ hy)
    have h1 : x * z * x⁻¹ ∈ S.Lbar ((h : G) * g) := by
      have := inv_mem (mul_mem (inv_mem hz1) (Subgroup.mem_inf.mp hfz).2)
      rwa [show (z⁻¹ * (z * x * z⁻¹ * x⁻¹))⁻¹ = x * z * x⁻¹ by group] at this
    have hzx : z ∈ S.Lbar (((x₀⁻¹ : S.M) : G) * ((h : G) * g)) := by
      rw [mem_Lbar_mul_iff, map_inv, inv_inv, hx₀]
      exact h1
    have hyea : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ea = ea + ec := by
      rcases mem_span_singleton_zmod2.mp (htrc y hy ea haPc) with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hya
      · rw [← h0]; abel
    have hQx : ((x₀⁻¹ : S.M) : G) * ((h : G) * g) * S.z *
        (((x₀⁻¹ : S.M) : G) * ((h : G) * g))⁻¹ ∈ S.QG := conj_mem_QG' S (x₀⁻¹).2 hcQ
    have hzx' : (((x₀⁻¹ : S.M) : G) * ((h : G) * g)) * S.z *
        (((x₀⁻¹ : S.M) : G) * ((h : G) * g))⁻¹ ≠ S.z :=
      conj_ne_z' S (x₀⁻¹).2 (conj_ne_z' S h.2 X.H.conj_ne)
    have hQy : (y₀ : G) * g * S.z * ((y₀ : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S y₀.2 haQ
    have hcl : S.cl ((y₀ : G) * g * S.z * ((y₀ : G) * g)⁻¹) =
        S.cl (((x₀⁻¹ : S.M) : G) * ((h : G) * g) * S.z *
          (((x₀⁻¹ : S.M) : G) * ((h : G) * g))⁻¹) := by
      rw [← ρ_cl_conj_z S y₀ haQ, ← ρ_cl_conj_z S (x₀⁻¹) hcQ, hy₀, hyea, map_inv, hx₀, ← hec,
        hxinv, add_comm]
    rw [← Lbar_eq_of_cl_eq S hQx hzx' hQy hcl, mem_Lbar_mul_iff, hy₀] at hzx
    have hyz : y * z = z * y := Lbar_comm S (conj_mem_QG' S h.2 haQ) hy hz1
    rwa [show y⁻¹ * z * y = z by rw [mul_assoc, ← hyz]; group] at hzx
  have hKA := le_sup_of_comm_hom hKab hcard hZK hcomm hf hJ
  intro l hl
  by_cases hlc : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ec = ec
  · exact hKA (Subgroup.mem_inf.mpr ⟨hl, hlc⟩)
  · have hlc' : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ec = ec + ea := by
      rcases mem_span_singleton_zmod2.mp (htra l hl ec hcP) with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hlc
      · rw [← h0]; abel
    have hlx : l * x ∈ S.Lbar g ⊓ vecStab S ec := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem hl hxL, ?_⟩
      rw [mem_vecStab, Subgroup.coe_mul, LinearEquiv.mul_apply, hxc', map_add, hlc',
        hfixa l hl, h2]
    have := mul_mem (hKA hlx) (mem_sup_left (inv_mem hxA))
    rwa [mul_inv_cancel_right] at this

end CFSG.LargeExtraspecial.S10

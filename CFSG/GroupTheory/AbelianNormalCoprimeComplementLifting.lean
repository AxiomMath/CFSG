module

public import Mathlib.GroupTheory.Complement
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.OrderOfElement

public noncomputable section

namespace CFSG.GroupTheory

open scoped Pointwise

namespace ComplementLifting

variable {G : Type*} [Group G] {N H K : Subgroup G} [N.Normal] [IsMulCommutative N]

omit [IsMulCommutative N] in
theorem existsUnique_part (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) {h : G} (hh : h ∈ H) :
    ∃! n : N, (n : G)⁻¹ * h ∈ K := by
  have hmem : h ∈ ((N ⊔ K : Subgroup G) : Set G) := by rw [hsup]; exact hh
  rw [Subgroup.normal_mul] at hmem
  obtain ⟨n, hn, k, hk, rfl⟩ := Set.mem_mul.mp hmem
  refine ⟨⟨n, hn⟩, by simpa only [inv_mul_cancel_left, SetLike.mem_coe] using hk, ?_⟩
  intro m hm
  have hmk : (m : G)⁻¹ * n ∈ K := by
    have h := K.mul_mem hm (K.inv_mem hk)
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using h
  have hmN : (m : G)⁻¹ * n ∈ N := N.mul_mem (N.inv_mem m.property) hn
  have hone : (m : G)⁻¹ * n = 1 := by
    have h : (m : G)⁻¹ * n ∈ N ⊓ K := ⟨hmN, hmk⟩
    rwa [hNK, Subgroup.mem_bot] at h
  exact Subtype.ext (inv_mul_eq_one.mp hone)

open Classical in
def part (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) (g : G) : N :=
  if hg : g ∈ H then (existsUnique_part hNK hsup hg).exists.choose else 1

omit [IsMulCommutative N] in
theorem part_spec (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) {h : G} (hh : h ∈ H) :
    ((part hNK hsup h : N) : G)⁻¹ * h ∈ K := by
  simp only [part, hh, ↓reduceDIte]
  exact (existsUnique_part hNK hsup hh).exists.choose_spec

omit [IsMulCommutative N] in
theorem part_eq (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) {h : G} (hh : h ∈ H) {n : N}
    (hn : (n : G)⁻¹ * h ∈ K) : part hNK hsup h = n :=
  (existsUnique_part hNK hsup hh).unique (part_spec hNK hsup hh) hn

omit [IsMulCommutative N] in
theorem part_of_mem (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) (n : N) :
    part hNK hsup (n : G) = n := by
  have hnH : (n : G) ∈ H := hsup ▸ Subgroup.mem_sup_left n.property
  exact part_eq hNK hsup hnH (by rw [inv_mul_cancel]; exact K.one_mem)

theorem conjNormal_of_mem (n m : N) : MulAut.conjNormal (n : G) m = m := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have h : n * m = m * n := (IsMulCommutative.is_comm (M := N)).comm n m
  have h' : (n : G) * m = m * n := congrArg Subtype.val h
  rw [h', mul_inv_cancel_right]

theorem part_mul (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) {h h₁ : G} (hh : h ∈ H)
    (hh₁ : h₁ ∈ H) :
    part hNK hsup (h * h₁) = part hNK hsup h * MulAut.conjNormal h (part hNK hsup h₁) := by
  apply part_eq hNK hsup (H.mul_mem hh hh₁)
  set n := part hNK hsup h
  set c := MulAut.conjNormal h (part hNK hsup h₁)
  have hc : (c : G) = h * (part hNK hsup h₁ : G) * h⁻¹ := MulAut.conjNormal_apply _ _
  have hcomm : n * c = c * n := (IsMulCommutative.is_comm (M := N)).comm n c
  have hinv : ((n * c : N) : G)⁻¹ = (n : G)⁻¹ * (c : G)⁻¹ := by
    rw [hcomm, Subgroup.coe_mul, mul_inv_rev]
  rw [hinv, hc]
  have heq : (n : G)⁻¹ * (h * (part hNK hsup h₁ : G) * h⁻¹)⁻¹ * (h * h₁) =
      ((n : G)⁻¹ * h) * (((part hNK hsup h₁ : N) : G)⁻¹ * h₁) := by
    simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
  rw [heq]
  exact K.mul_mem (part_spec hNK hsup hh) (part_spec hNK hsup hh₁)

theorem out_inv_mul_mem (g : G) (x : G ⧸ H) : (g • x).out⁻¹ * g * x.out ∈ H := by
  have h : ((g • x).out : G ⧸ H) = ((g * x.out : G) : G ⧸ H) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  rw [mul_assoc]
  exact QuotientGroup.eq.mp h

abbrev commGroupOf (N : Subgroup G) [IsMulCommutative N] : CommGroup N :=
  .mk (IsMulCommutative.is_comm (M := N)).comm

attribute [local instance] commGroupOf

variable [Fintype (G ⧸ H)]

def transferPart (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) (g : G) : N :=
  ∏ x : G ⧸ H, MulAut.conjNormal (g • x).out (part hNK hsup ((g • x).out⁻¹ * g * x.out))

theorem transferPart_mul (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) (g g₁ : G) :
    transferPart hNK hsup (g * g₁) =
      transferPart hNK hsup g * MulAut.conjNormal g (transferPart hNK hsup g₁) := by
  have hterm : ∀ x : G ⧸ H,
      MulAut.conjNormal ((g * g₁) • x).out
          (part hNK hsup (((g * g₁) • x).out⁻¹ * (g * g₁) * x.out)) =
        MulAut.conjNormal (g • (g₁ • x)).out
            (part hNK hsup ((g • (g₁ • x)).out⁻¹ * g * (g₁ • x).out)) *
          MulAut.conjNormal g (MulAut.conjNormal (g₁ • x).out
            (part hNK hsup ((g₁ • x).out⁻¹ * g₁ * x.out))) := by
    intro x
    rw [mul_smul]
    set y := g₁ • x
    have hsplit : (g • y).out⁻¹ * (g * g₁) * x.out =
        ((g • y).out⁻¹ * g * y.out) * (y.out⁻¹ * g₁ * x.out) := by group
    rw [hsplit, part_mul hNK hsup (out_inv_mul_mem g y) (out_inv_mul_mem g₁ x), map_mul]
    congr 1
    have hcancel : (g • y).out * ((g • y).out⁻¹ * g * y.out) = g * y.out := by group
    rw [← MulAut.mul_apply, ← map_mul, hcancel, map_mul, MulAut.mul_apply]
  unfold transferPart
  rw [Finset.prod_congr rfl (fun x _ => hterm x), Finset.prod_mul_distrib, map_prod]
  congr 1
  exact Equiv.prod_comp (MulAction.toPerm g₁) (fun y : G ⧸ H => MulAut.conjNormal (g • y).out
    (part hNK hsup ((g • y).out⁻¹ * g * y.out)))

theorem transferPart_of_mem (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) (n : N) :
    transferPart hNK hsup (n : G) = n ^ Fintype.card (G ⧸ H) := by
  have hNH : N ≤ H := hsup ▸ le_sup_left
  have hterm : ∀ x : G ⧸ H, MulAut.conjNormal ((n : G) • x).out
      (part hNK hsup (((n : G) • x).out⁻¹ * n * x.out)) = n := by
    intro x
    have hfix : (n : G) • x = x := by
      rw [← QuotientGroup.out_eq' x, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      apply hNH
      have h := ‹N.Normal›.conj_mem _ (N.inv_mem n.property) (x.out)⁻¹
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
    rw [hfix]
    have hmem : (x.out)⁻¹ * n * x.out ∈ N := by
      simpa only [inv_inv] using ‹N.Normal›.conj_mem _ n.property (x.out)⁻¹
    rw [part_of_mem hNK hsup ⟨_, hmem⟩]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    group
  unfold transferPart
  rw [Finset.prod_congr rfl (fun x _ => hterm x), Finset.prod_const, Finset.card_univ]

end ComplementLifting

open ComplementLifting in
theorem abelian_normal_coprime_index_complement_lifting {G : Type*} [Group G] [Finite G]
    (N H K : Subgroup G) [N.Normal] [IsMulCommutative N] (hcop : Nat.Coprime H.index (Nat.card N))
    (hNK : N ⊓ K = ⊥) (hsup : N ⊔ K = H) :
    ∃ D : Subgroup G, Subgroup.IsComplement' N D ∧ N ⊓ D = ⊥ ∧ N ⊔ D = ⊤ := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _
  let _ : CommGroup N := commGroupOf N
  have hm : Fintype.card (G ⧸ H) = H.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_of_coprime 1 (hm ▸ hcop) Nat.card_pos.ne'
  have hroot : ∀ n : N, (n ^ Fintype.card (G ⧸ H)) ^ r = n := by
    intro n
    rw [← pow_mul, ← pow_mod_natCard, hr, pow_mod_natCard, pow_one]
  let c : G → N := fun g => transferPart hNK hsup g ^ r
  have hc_mul : ∀ g g₁ : G, c (g * g₁) = c g * MulAut.conjNormal g (c g₁) := by
    intro g g₁
    simp only [c, transferPart_mul, mul_pow, map_pow]
  have hc_mem : ∀ n : N, c n = n := fun n => by simp only [c, transferPart_of_mem, hroot]
  have hc_one : c 1 = 1 := by
    have h := hc_mul 1 1
    rw [mul_one, map_one, MulAut.one_apply] at h
    exact left_eq_mul.mp h
  let D : Subgroup G :=
    { carrier := {g | c g = 1}
      one_mem' := hc_one
      mul_mem' := by
        intro a b ha hb
        change c (a * b) = 1
        rw [hc_mul, show c a = 1 from ha, show c b = 1 from hb, map_one, mul_one]
      inv_mem' := by
        intro a ha
        change c a⁻¹ = 1
        have h := hc_mul a⁻¹ a
        rw [inv_mul_cancel, hc_one, show c a = 1 from ha, map_one, mul_one] at h
        exact h.symm }
  have hdisj : N ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : c g = 1 := hg.2
    rw [show g = ((⟨g, hg.1⟩ : N) : G) from rfl, hc_mem] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hmul : (N : Set G) * (D : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => Set.mem_mul.mpr
      ⟨(c g : G), (c g).property, (c g : G)⁻¹ * g, ?_, by group⟩
    change c ((c g : G)⁻¹ * g) = 1
    rw [hc_mul, ← Subgroup.coe_inv, hc_mem, conjNormal_of_mem, inv_mul_cancel]
  have hcompl : Subgroup.IsComplement' N D :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hdisj) hmul
  exact ⟨D, hcompl, hdisj, hcompl.sup_eq_top⟩

end CFSG.GroupTheory

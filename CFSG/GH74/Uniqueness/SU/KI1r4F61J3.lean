module

public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate5149
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Sp

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Blueprint

theorem fourGenOK_spec {n : ℕ} (hn : n < 2 ^ 32) {gs : List Table} {i j : ℕ}
    (h : fourGenOK n gs i j = true) :
    ∃ u v : Equiv.Perm (Fin n), u ∈ closure (tp n '' {x | x ∈ gs.toArray}) ∧
      v ∈ closure (tp n '' {x | x ∈ gs.toArray}) ∧ orderOf u = 2 ∧ orderOf v = 2 ∧
      u * v = v * u ∧ u ≠ v := by
  simp only [fourGenOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hi, hj⟩, hperm⟩, hinvI⟩, hinvJ⟩, hcomm⟩, hne⟩ := h
  have hmem : ∀ k, k < gs.length → gs[k]! ∈ gs := fun k hk => by
    rw [getElem!_pos gs k hk]
    exact List.getElem_mem hk
  have hrepI := rep_tp (hperm _ (hmem i hi))
  have hrepJ := rep_tp (hperm _ (hmem j hj))
  refine ⟨tp n gs[i]!, tp n gs[j]!, subset_closure ⟨_, ?_, rfl⟩, subset_closure ⟨_, ?_, rfl⟩,
    orderOf_eq_two_of_involOK hn hrepI hinvI, orderOf_eq_two_of_involOK hn hrepJ hinvJ,
    (commTT_iff hrepI hrepJ).1 hcomm, ?_⟩
  · simpa using hmem i hi
  · simpa using hmem j hj
  · intro heq
    have h1 := (tblEq_iff_eq hrepI hrepJ).2 heq
    rw [hne] at h1
    exact Bool.false_ne_true h1

theorem modE4_of_fourGenOK {n : ℕ} (hn : n < 2 ^ 32) {G : Subgroup (Equiv.Perm (Fin n))}
    {t : Equiv.Perm (Fin n)} {gs : List Table} {i j : ℕ} (h : fourGenOK n gs i j = true)
    (hC : closure (tp n '' {x | x ∈ gs.toArray}) =
      G ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin n)))) : ModE4 G t := by
  obtain ⟨u, v, hu, hv, hu2, hv2, huv, hne⟩ := fourGenOK_spec hn h
  rw [hC] at hu hv
  obtain ⟨huG, huc⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hvG, hvc⟩ := Subgroup.mem_inf.1 hv
  have hu1 : u ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hv1 : v ≠ 1 := fun h => by
    rw [h, orderOf_one] at hv2
    exact absurd hv2 (by norm_num)
  exact ⟨u, v, huG, hvG, hu1, hv1, hne, hu2 ▸ pow_orderOf_eq_one u, hv2 ▸ pow_orderOf_eq_one v, huv,
    (Subgroup.mem_centralizer_singleton_iff.1 huc).symm,
    (Subgroup.mem_centralizer_singleton_iff.1 hvc).symm⟩

theorem modE4_j3_outer :
    ∀ g ∈ j3R, g ^ 2 = 1 → g ∉ j3P → ModE4 j3P g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hrows, hcover, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  intro g hgR hg2 hgP
  have hg1 : g ≠ 1 := fun h => hgP (h ▸ j3P.one_mem)
  have hord : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  obtain ⟨r, hr, c, hc, hgc⟩ := hcover g hgR hord
  obtain ⟨-, -, hout, hCeq, -, -⟩ := hrows r hr
  have hrout : r.outer = true := by
    by_contra hnot
    apply hgP
    rw [hgc]
    have hmem : tp 6156 r.rep ∈ j3P := by
      by_contra hn
      exact hnot (hout.2 hn)
    exact j3P.mul_mem (j3P.mul_mem hc hmem) (j3P.inv_mem hc)
  have hcheck : fourGenOK 6156 r.centGens 0 1 = true := by
    have := List.all_eq_true.1 Certificates.certificate5149 r hr
    simpa [hrout] using this
  have h4 : ModE4 j3P (tp 6156 r.rep) :=
    modE4_of_fourGenOK (by norm_num) hcheck (G := j3P) (t := tp 6156 r.rep) hCeq
  rw [hgc]
  exact h4.conj hc

theorem fixed_four_of_pair {K : Type} [Group K] [Finite K] (α : MulAut K) {a b : K} (ha2 : a ^ 2 = 1)
    (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hcomm : a * b = b * a)
    (hfa : α a = a) (hfb : α b = b) :
    ∃ V : Subgroup K, (∀ v ∈ V, α v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  have hya : b ∉ zpowers a := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers_sq ha2 hmem with h | h
    · exact hb1 h
    · exact hab h.symm
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := a) (y := b)
    ha2 hb2 ha1 hya hcomm
  have hle : zpowers a ⊔ zpowers b ≤ fixedSub K α :=
    sup_le (Subgroup.zpowers_le.2 hfa) (Subgroup.zpowers_le.2 hfb)
  exact ⟨zpowers a ⊔ zpowers b, fun v hv => hle hv, hel, by rw [hcard]; norm_num⟩

theorem outerFourSp_J3 :
    OuterFourSp .J3 := by
  intro K _ _ ⟨e⟩ α hα2 hαout
  have hM := j3_autModel
  have e' : K ≃* NativeSporadic.J3 := e
  let θ : K ≃* ↥j3P := e'.trans j3PermEquiv
  have hααk : ∀ k : K, α (α k) = k := fun k => by
    have := congrArg (fun γ : MulAut K => γ k) hα2
    simpa [pow_two] using this
  obtain ⟨x, hxR, hx⟩ := hM.surj (MulAut.congr θ α)
  have hx' : ∀ k : K, ((θ (α k) : ↥j3P) : Equiv.Perm (Fin 6156)) =
      x * (θ k : Equiv.Perm (Fin 6156)) * x⁻¹ := fun k => by
    have := hx (θ k)
    simpa [MulAut.congr_apply] using this
  have hxx : x * x = 1 := by
    refine hM.inj (x * x) (j3R.mul_mem hxR hxR) fun p hp => ?_
    set k : K := θ.symm ⟨p, hp⟩ with hkdef
    have hk : ((θ k : ↥j3P) : Equiv.Perm (Fin 6156)) = p :=
      congrArg Subtype.val (θ.apply_symm_apply ⟨p, hp⟩)
    have key : p = x * (x * p * x⁻¹) * x⁻¹ := by
      have h1 := hx' (α k)
      rw [hααk, hx' k, hk] at h1
      exact h1
    calc x * x * p = (x * (x * p * x⁻¹) * x⁻¹) * (x * x) := by group
      _ = p * (x * x) := by rw [← key]
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hαout
    refine ⟨1, MulEquiv.ext fun k => ?_⟩
    have h1 := hx' k
    simp only [one_mul, inv_one, mul_one] at h1
    have h2 : θ (α k) = θ k := Subtype.ext h1
    simpa using θ.injective h2
  have hxP : x ∉ j3P := by
    intro hxP
    apply hαout
    refine ⟨θ.symm ⟨x, hxP⟩, MulEquiv.ext fun k => ?_⟩
    apply θ.injective
    apply Subtype.ext
    rw [hx' k]
    simp [MulAut.conj_apply]
  obtain ⟨u, v, hu, hv, hu1, hv1, huv', hu2, hv2, huv, hxu, hxv⟩ :=
    modE4_j3_outer x hxR (by rw [pow_two]; exact hxx) hxP
  set a : K := θ.symm ⟨u, hu⟩ with hadef
  set b : K := θ.symm ⟨v, hv⟩ with hbdef
  have hθa : ((θ a : ↥j3P) : Equiv.Perm (Fin 6156)) = u :=
    congrArg Subtype.val (θ.apply_symm_apply ⟨u, hu⟩)
  have hθb : ((θ b : ↥j3P) : Equiv.Perm (Fin 6156)) = v :=
    congrArg Subtype.val (θ.apply_symm_apply ⟨v, hv⟩)
  have hfa : α a = a := by
    apply θ.injective
    apply Subtype.ext
    rw [hx' a, hθa]
    calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [hxu]
      _ = u := by group
  have hfb : α b = b := by
    apply θ.injective
    apply Subtype.ext
    rw [hx' b, hθb]
    calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [hxv]
      _ = v := by group
  have ha2 : a ^ 2 = 1 := by
    apply θ.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, hθa, hu2, map_one, Subgroup.coe_one]
  have hb2 : b ^ 2 = 1 := by
    apply θ.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, hθb, hv2, map_one, Subgroup.coe_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hu1
    rw [← hθa, h, map_one, Subgroup.coe_one]
  have hb1 : b ≠ 1 := by
    intro h
    apply hv1
    rw [← hθb, h, map_one, Subgroup.coe_one]
  have hab : a ≠ b := by
    intro h
    apply huv'
    rw [← hθa, ← hθb, h]
  have hcomm : a * b = b * a := by
    apply θ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hθa, hθb]
    exact huv
  exact fixed_four_of_pair α ha2 hb2 ha1 hb1 hab hcomm hfa hfb

end CFSG.GH74.Uniqueness.SU.K.R4

module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Qmax

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

section Abstract

theorem card_map_mul_card_ker_inf {M N : Type*} [Group M] [Group N] (f : M →* N)
    (S : Subgroup M) : Nat.card (S.map f) * Nat.card (f.ker ⊓ S : Subgroup M) = Nat.card S := by
  rw [← Subgroup.relIndex_ker f (K := S), Subgroup.relIndex_mul_card]

theorem sup_cs_ker_eq_top {M : Type*} [Group M] [Finite M] (π : M →* alternatingGroup (Fin 5))
    {A Y : Subgroup M} (hYA : Y ≤ A) (hY4 : Nat.card Y = 4) (hYk : Y ⊓ π.ker = ⊥)
    (hA4 : Nat.card (A.map π) ≤ 4) (m : M)
    (hne : ∃ a ∈ A, ∀ a' ∈ A, a'⁻¹ * (m⁻¹ * a * m) ∉ π.ker) :
    ∀ x : M, ∃ h ∈ A ⊔ cs m Y, h⁻¹ * x ∈ π.ker := by
  have hPcard : Nat.card (Y.map π) = 4 := by
    have h := card_map_mul_card_ker_inf π Y
    rw [inf_comm, hYk, Subgroup.card_bot, mul_one] at h
    rw [h, hY4]
  have hP : Y.map π = A.map π :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hYA) (by rw [hPcard]; exact hA4)
  have hP'card : Nat.card (cs (π m) (Y.map π)) = 4 := (nat_card_cs _ _).trans hPcard
  have hPne : Y.map π ≠ cs (π m) (Y.map π) := by
    intro heq
    obtain ⟨a, haA, ha⟩ := hne
    have h1 : π a ∈ cs (π m) (Y.map π) := by
      rw [← heq, hP]
      exact ⟨a, haA, rfl⟩
    have h2 : (π m)⁻¹ * π a * π m ∈ Y.map π := mem_cs.1 h1
    rw [hP] at h2
    obtain ⟨a', ha', ha'e⟩ := h2
    refine ha a' ha' ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha'e, map_mul, map_mul, map_inv]
    exact inv_mul_cancel _
  have hle1 : Y.map π ≤ (A ⊔ cs m Y).map π :=
    Subgroup.map_mono (hYA.trans le_sup_left)
  have hle2 : cs (π m) (Y.map π) ≤ (A ⊔ cs m Y).map π := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := mem_cs.1 hx
    refine ⟨m * y * m⁻¹, mem_sup_right (mem_cs_iff.2 hy), ?_⟩
    rw [map_mul, map_mul, map_inv, hyx]
    group
  have htop : (A ⊔ cs m Y).map π = ⊤ :=
    a5_eq_top_of_two_sylow hPcard hP'card hPne hle1 hle2
  intro x
  have hx : π x ∈ (A ⊔ cs m Y).map π := by
    rw [htop]
    trivial
  obtain ⟨h, hh, hhx⟩ := hx
  exact ⟨h, hh, by rw [MonoidHom.mem_ker, map_mul, map_inv, hhx, inv_mul_cancel]⟩

theorem eq_of_forall_mul_central {G : Type} [Group G] {M H : Subgroup G} (hM : ⁅M, M⁆ = M)
    (hHM : H ≤ M)
    (hdec : ∀ x ∈ M, ∃ u ∈ H, ∃ z ∈ M, (∀ n ∈ M, z * n = n * z) ∧ x = u * z) : H = M := by
  refine le_antisymm hHM ?_
  calc M = ⁅M, M⁆ := hM.symm
    _ ≤ H := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨u, hu, z, hz, hzc, rfl⟩ := hdec x hx
      obtain ⟨v, hv, z', hz', hzc', rfl⟩ := hdec y hy
      have hz1 : ⁅z, z'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hzc z' hz')
      rw [commutator_mul_of_comm (hzc u (hHM hu)) (hzc v (hHM hv)) (hzc' u (hHM hu))
        (hzc' v (hHM hv)), hz1, mul_one]
      exact commutator_self_le H (commutator_mem_commutator hu hv)

end Abstract

section Decomp

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {c : CaseB A R t}
  {M₁ M₂ : Subgroup G}

theorem CaseB.Factors.sylow_inf_cent_eq (F : c.Factors M₁ M₂) {A₁ : Subgroup G}
    (hA₁ : IsSylowOf 2 A₁ M₁) (hXA : c.W ⊓ M₁ ≤ A₁) :
    A₁ ⊓ (M₁ ⊓ centralizer (c.W : Set G)) = c.W ⊓ M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact F.sylow_W₁.eq_of_le (le_inf hXA F.sylow_W₁.le) inf_le_right hA₁.isPGroup.to_inf_left

theorem CaseB.Factors.exists_central_decomp (F : c.Factors M₁ M₂) (hZ : c.OddCoreCentral)
    {k : G} (hkM : k ∈ M₁) (hkC : k ∈ centralizer (c.W : Set G)) :
    ∃ x ∈ c.W ⊓ M₁, ∃ z ∈ M₁, (∀ n ∈ M₁, z * n = n * z) ∧ k = x * z := by
  have hM₁N : M₁ ≤ c.Ninf := F.M₁_le
  obtain ⟨O₁, -, hO₁odd, -, hO₁dec, hO₁norm, -⟩ := F.exists_O₁
  obtain ⟨w, hw, o, ho, hk⟩ := hO₁dec k hkC
  have hoN : o ∈ c.Ninf := by
    have : o = w⁻¹ * k := by rw [hk]; group
    rw [this]
    exact c.Ninf.mul_mem (c.Ninf.inv_mem (F.W_le hw)) (hM₁N hkM)
  have hodd : Odd (Nat.card ↥(O₁ ⊓ c.Ninf)) :=
    hO₁odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hocent : ∀ n ∈ c.Ninf, o * n = n * o := fun n hn =>
    hZ (O₁ ⊓ c.Ninf) inf_le_right (fun x hx q hq =>
      ⟨hO₁norm x hx q hq.1, c.Ninf.mul_mem (c.Ninf.mul_mem hx hq.2) (c.Ninf.inv_mem hx)⟩)
      hodd o ⟨ho, hoN⟩ n hn
  have hwF : w ∈ (c.W ⊓ M₁) ⊔ (c.W ⊓ M₂) := by rw [F.W_eq]; exact hw
  obtain ⟨f₁, hf₁, f₂, hf₂, hw12⟩ := mem_sup_of_forall_comm (O := c.W ⊓ M₁) (E := c.W ⊓ M₂)
    (fun x hx y hy => comm_of_isElemAbelian_two c.W_elem hx.1 hy.1) hwF
  refine ⟨f₁, hf₁, f₂ * o, ?_, fun n hn => ?_, ?_⟩
  · have : f₂ * o = f₁⁻¹ * k := by rw [hk, hw12]; group
    rw [this]
    exact M₁.mul_mem (M₁.inv_mem hf₁.2) hkM
  · have h1 : f₂ * n = n * f₂ := (mem_centralizer_iff.mp (F.W₂_cent hf₂) n hn).symm
    have h2 : o * n = n * o := hocent n (hM₁N hn)
    calc f₂ * o * n = f₂ * (o * n) := by group
      _ = f₂ * (n * o) := by rw [h2]
      _ = (f₂ * n) * o := by group
      _ = (n * f₂) * o := by rw [h1]
      _ = n * (f₂ * o) := by group
  · rw [hk, hw12]; group

theorem CaseB.Factors.exists_mul_ker (F : c.Factors M₁ M₂)
    {A₁ : Subgroup G} (hA₁ : IsSylowOf 2 A₁ M₁) (hXA : c.W ⊓ M₁ ≤ A₁) {m : G} (hm : m ∈ M₁)
    {Y Yg Yp : Subgroup G} (hY : Y ≤ A₁) (hY4 : Nat.card ↥Y = 4) (hYW : Y ⊓ c.W = ⊥)
    (hYg : Yg ≤ c.W ⊓ M₁) (hYgc : ∀ y ∈ Yg, ∀ a ∈ A₁, y * a = a * y)
    (hYp : cs m Yg = Yp) (hYpc : ¬ ∀ y ∈ Yp, ∀ a ∈ A₁, y * a = a * y) :
    ∀ x ∈ M₁, ∃ h ∈ A₁ ⊔ cs m Y, h⁻¹ * x ∈ centralizer (c.W : Set G) := by
  subst hYp
  obtain ⟨π, -, hπk⟩ := F.a5₁
  have hA₁M : A₁ ≤ M₁ := hA₁.le
  have hYM : Y ≤ M₁ := hY.trans hA₁M
  have hK : A₁ ⊓ (M₁ ⊓ centralizer (c.W : Set G)) = c.W ⊓ M₁ := F.sylow_inf_cent_eq hA₁ hXA
  have hYA : Y.subgroupOf M₁ ≤ A₁.subgroupOf M₁ := fun y hy =>
    mem_subgroupOf.2 (hY (mem_subgroupOf.1 hy))
  have hY4' : Nat.card ↥(Y.subgroupOf M₁) = 4 := by
    rw [← hY4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv
  have hYk : Y.subgroupOf M₁ ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyY, hyk⟩
    have hyC : (y : G) ∈ centralizer (c.W : Set G) := (hπk y).1 (MonoidHom.mem_ker.1 hyk)
    have hyX : (y : G) ∈ c.W ⊓ M₁ := by
      rw [← hK]
      exact ⟨hY (mem_subgroupOf.1 hyY), y.2, hyC⟩
    have hy1 : (y : G) ∈ Y ⊓ c.W := ⟨mem_subgroupOf.1 hyY, hyX.1⟩
    rw [hYW] at hy1
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hy1))
  have hA4 : Nat.card ↥((A₁.subgroupOf M₁).map π) ≤ 4 := by
    have h1 := card_map_mul_card_ker_inf π (A₁.subgroupOf M₁)
    have h2 : Nat.card ↥(A₁.subgroupOf M₁) = 64 := by
      rw [← F.sylow_card₁ A₁ hA₁]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁M).toEquiv
    have hle : (c.W ⊓ M₁).subgroupOf M₁ ≤ π.ker ⊓ A₁.subgroupOf M₁ := by
      intro x hx
      have hxk : x ∈ π.ker := by
        rw [MonoidHom.mem_ker, hπk, mem_centralizer_iff]
        intro w hw
        exact comm_of_isElemAbelian_two c.W_elem hw (mem_subgroupOf.1 hx).1
      exact ⟨hxk, mem_subgroupOf.2 (hXA (mem_subgroupOf.1 hx))⟩
    have h3 : 16 ≤ Nat.card ↥(π.ker ⊓ A₁.subgroupOf M₁) := by
      calc 16 = Nat.card ↥(c.W ⊓ M₁) := F.card₁.symm
        _ = Nat.card ↥((c.W ⊓ M₁).subgroupOf M₁) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
        _ ≤ _ := Subgroup.card_le_of_le hle
    by_contra hcon
    have h4 : 5 * 16 ≤ Nat.card ↥((A₁.subgroupOf M₁).map π) *
        Nat.card ↥(π.ker ⊓ A₁.subgroupOf M₁) := Nat.mul_le_mul (by omega) h3
    omega
  have hne : ∃ a ∈ A₁.subgroupOf M₁, ∀ a' ∈ A₁.subgroupOf M₁,
      a'⁻¹ * ((⟨m, hm⟩ : ↥M₁)⁻¹ * a * ⟨m, hm⟩) ∉ π.ker := by
    by_contra hcon
    push Not at hcon
    refine hYpc fun z hz a ha => ?_
    have hz' : m⁻¹ * z * m ∈ Yg := mem_cs.1 hz
    obtain ⟨a', ha', hk⟩ := hcon ⟨a, hA₁M ha⟩ (mem_subgroupOf.2 ha)
    have hkC := (hπk _).1 (MonoidHom.mem_ker.1 hk)
    have h1 : Commute (m⁻¹ * z * m) (a' : G) := hYgc _ hz' _ (mem_subgroupOf.1 ha')
    have h2 : Commute (m⁻¹ * z * m) ((a' : G)⁻¹ * (m⁻¹ * a * m)) :=
      (mem_centralizer_iff.1 hkC _ (hYg hz').1)
    have h3 := Commute.mul_right h1 h2
    have e : (a' : G) * ((a' : G)⁻¹ * (m⁻¹ * a * m)) = m⁻¹ * a * m := by group
    rw [e] at h3
    have h4 : m⁻¹ * (z * a) * m = m⁻¹ * (a * z) * m := by
      calc m⁻¹ * (z * a) * m = (m⁻¹ * z * m) * (m⁻¹ * a * m) := by group
        _ = (m⁻¹ * a * m) * (m⁻¹ * z * m) := h3.eq
        _ = m⁻¹ * (a * z) * m := by group
    exact mul_left_cancel (mul_right_cancel h4)
  have key := sup_cs_ker_eq_top π hYA hY4' hYk hA4 (⟨m, hm⟩ : ↥M₁) hne
  intro x hx
  obtain ⟨h, hh, hhk⟩ := key ⟨x, hx⟩
  have hle : A₁.subgroupOf M₁ ⊔ cs (⟨m, hm⟩ : ↥M₁) (Y.subgroupOf M₁) ≤
      (A₁ ⊔ cs m Y).subgroupOf M₁ := by
    refine sup_le (fun a ha => mem_subgroupOf.2 (mem_sup_left (mem_subgroupOf.1 ha))) ?_
    intro y hy
    exact mem_subgroupOf.2 (mem_sup_right (mem_cs.2 (mem_subgroupOf.1 (mem_cs.1 hy))))
  exact ⟨(h : G), mem_subgroupOf.1 (hle hh), (hπk _).1 (MonoidHom.mem_ker.1 hhk)⟩

theorem CaseB.Factors.eq_sup_cs_of_moves (F : c.Factors M₁ M₂) (hZ : c.OddCoreCentral)
    {A₁ : Subgroup G} (hA₁ : IsSylowOf 2 A₁ M₁) (hXA : c.W ⊓ M₁ ≤ A₁) {m : G} (hm : m ∈ M₁)
    {Y Yg Yp : Subgroup G} (hY : Y ≤ A₁) (hY4 : Nat.card ↥Y = 4) (hYW : Y ⊓ c.W = ⊥)
    (hYg : Yg ≤ c.W ⊓ M₁) (hYgc : ∀ y ∈ Yg, ∀ a ∈ A₁, y * a = a * y)
    (hYp : cs m Yg = Yp) (hYpc : ¬ ∀ y ∈ Yp, ∀ a ∈ A₁, y * a = a * y) :
    A₁ ⊔ cs m Y = M₁ := by
  have hA₁M : A₁ ≤ M₁ := hA₁.le
  have hcsM : cs m Y ≤ M₁ := by
    intro y hy
    have h1 : m⁻¹ * y * m ∈ M₁ := hA₁M (hY (mem_cs.1 hy))
    have h2 := M₁.mul_mem (M₁.mul_mem hm h1) (M₁.inv_mem hm)
    have e : m * (m⁻¹ * y * m) * m⁻¹ = y := by group
    rwa [e] at h2
  have hHM : A₁ ⊔ cs m Y ≤ M₁ := sup_le hA₁M hcsM
  refine eq_of_forall_mul_central F.perfect₁ hHM ?_
  intro x hx
  obtain ⟨h, hh, hk⟩ := F.exists_mul_ker hA₁ hXA hm hY hY4 hYW hYg hYgc hYp hYpc x hx
  have hhM : h ∈ M₁ := hHM hh
  obtain ⟨x', hx', z, hz, hzc, hkz⟩ :=
    F.exists_central_decomp hZ (M₁.mul_mem (M₁.inv_mem hhM) hx) hk
  refine ⟨h * x', (A₁ ⊔ cs m Y).mul_mem hh (mem_sup_left (hXA hx')), z, hz, hzc, ?_⟩
  calc x = h * (h⁻¹ * x) := by group
    _ = h * (x' * z) := by rw [hkz]
    _ = h * x' * z := by group

end Decomp

end CFSG.OddStandard.Seitz77

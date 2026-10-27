module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Inputs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin Subgroup

theorem inv_eq_self_of_sq_eq_one' {G : Type*} [Group G] {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h)

structure TIPair {G : Type*} [Group G] (V A : Subgroup G) : Prop where
  V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  V_exp : ∀ a ∈ V, a ^ 2 = 1
  A_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  A_exp : ∀ a ∈ A, a ^ 2 = 1
  V_TI : fusionIsTI V
  A_TI : fusionIsTI A
  inf_bot : V ⊓ A = ⊥

theorem mem_normalizer_of_commute_of_TI {G : Type*} [Group G] {V : Subgroup G} (hV : fusionIsTI V)
    {u g : G} (hu : u ∈ V) (hu1 : u ≠ 1) (hc : g * u = u * g) :
    g ∈ normalizer (V : Set G) := by
  have hne : V ⊓ conjR V g ≠ ⊥ := by
    intro hb
    have hmem : u ∈ V ⊓ conjR V g := by
      refine Subgroup.mem_inf.mpr ⟨hu, ?_⟩
      rw [mem_conjR]
      have e : g * u * g⁻¹ = u := by rw [hc]; group
      rw [e]
      exact hu
    rw [hb, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  exact conjR_eq_self_iff.mp (conjR_eq_of_inf_ne_bot hV hne)

theorem exists_commute_of_normalizer {G : Type*} [Group G] {A : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAe : ∀ a ∈ A, a ^ 2 = 1) (hA : A ≠ ⊥) {u : G}
    (hu : u ∈ normalizer (A : Set G)) (hu2 : u ^ 2 = 1) :
    ∃ a ∈ A, a ≠ 1 ∧ u * a = a * u := by
  obtain ⟨⟨a₀, ha₀⟩, ha₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have ha₀1 : a₀ ≠ 1 := fun h => ha₀1' (Subtype.ext h)
  have hui : u⁻¹ = u := inv_eq_self_of_sq_eq_one' hu2
  have huu : u * u = 1 := by simpa [pow_two] using hu2
  have hb : u⁻¹ * a₀ * u⁻¹⁻¹ ∈ A := (mem_normalizer_iff.mp (inv_mem hu) a₀).mp ha₀
  rw [inv_inv, hui] at hb
  obtain ⟨b, hbdef⟩ : ∃ b, b = u * a₀ * u := ⟨_, rfl⟩
  rw [← hbdef] at hb
  have hub : u * b * u = a₀ := by
    calc u * b * u = (u * u) * a₀ * (u * u) := by rw [hbdef]; group
      _ = a₀ := by rw [huu, one_mul, mul_one]
  by_cases h : a₀ * b = 1
  · refine ⟨a₀, ha₀, ha₀1, ?_⟩
    have ha2 : a₀ * a₀ = 1 := by simpa [pow_two] using hAe a₀ ha₀
    have e1 : b = a₀ := mul_left_cancel (a := a₀) (h.trans ha2.symm)
    have e2 : u * a₀ * u = a₀ := by rw [← hbdef, e1]
    calc u * a₀ = u * a₀ * (u * u) := by rw [huu, mul_one]
      _ = (u * a₀ * u) * u := by group
      _ = a₀ * u := by rw [e2]
  · refine ⟨a₀ * b, A.mul_mem ha₀ hb, h, ?_⟩
    have hcomm := hAc a₀ ha₀ b hb
    have h1 : u * (a₀ * b) * u = a₀ * b := by
      calc u * (a₀ * b) * u = (u * a₀ * u) * (u * b * u) := by
            calc u * (a₀ * b) * u = u * a₀ * (u * u) * b * u := by rw [huu, mul_one]; group
              _ = (u * a₀ * u) * (u * b * u) := by group
        _ = b * a₀ := by rw [← hbdef, hub]
        _ = a₀ * b := hcomm.symm
    calc u * (a₀ * b) = u * (a₀ * b) * (u * u) := by rw [huu, mul_one]
      _ = (u * (a₀ * b) * u) * u := by group
      _ = (a₀ * b) * u := by rw [h1]

namespace TIPair

variable {G : Type*} [Group G] {V A : Subgroup G}

theorem symm (hp : TIPair V A) : TIPair A V :=
  ⟨hp.A_comm, hp.A_exp, hp.V_comm, hp.V_exp, hp.A_TI, hp.V_TI, by rw [inf_comm]; exact hp.inf_bot⟩

theorem commute_of_mem (hp : TIPair V A) {u a : G} (hu : u ∈ V ⊓ normalizer (A : Set G))
    (ha : a ∈ A ⊓ normalizer (V : Set G)) : u * a = a * u := by
  have h1 : u⁻¹ * a⁻¹ * u * a ∈ V := by
    have h1' : a⁻¹ * u * a⁻¹⁻¹ ∈ V := (mem_normalizer_iff.mp (inv_mem ha.2) u).mp hu.1
    have e : u⁻¹ * a⁻¹ * u * a = u⁻¹ * (a⁻¹ * u * a⁻¹⁻¹) := by group
    rw [e]
    exact V.mul_mem (V.inv_mem hu.1) h1'
  have h2 : u⁻¹ * a⁻¹ * u * a ∈ A := by
    have h2' : u⁻¹ * a⁻¹ * u⁻¹⁻¹ ∈ A :=
      (mem_normalizer_iff.mp (inv_mem hu.2) a⁻¹).mp (A.inv_mem ha.1)
    have e : u⁻¹ * a⁻¹ * u * a = (u⁻¹ * a⁻¹ * u⁻¹⁻¹) * a := by group
    rw [e]
    exact A.mul_mem h2' ha.1
  have h3 : u⁻¹ * a⁻¹ * u * a ∈ V ⊓ A := ⟨h1, h2⟩
  rw [hp.inf_bot, Subgroup.mem_bot] at h3
  calc u * a = a * u * (u⁻¹ * a⁻¹ * u * a) := by group
    _ = a * u := by rw [h3, mul_one]

theorem commutator_mem (hp : TIPair V A) {b v : G} (hb : b ∈ A ⊓ normalizer (V : Set G))
    (hv : v ∈ V) : b⁻¹ * v * b * v⁻¹ ∈ V ⊓ normalizer (A : Set G) := by
  have hbV : b⁻¹ * v * b⁻¹⁻¹ ∈ V := (mem_normalizer_iff.mp (inv_mem hb.2) v).mp hv
  have hcV : b⁻¹ * v * b * v⁻¹ ∈ V := by
    have e : b⁻¹ * v * b * v⁻¹ = (b⁻¹ * v * b⁻¹⁻¹) * v⁻¹ := by group
    rw [e]
    exact V.mul_mem hbV (V.inv_mem hv)
  refine Subgroup.mem_inf.mpr ⟨hcV, ?_⟩
  by_cases hb1 : b = 1
  · subst hb1
    simp only [inv_one, one_mul, mul_one, mul_inv_cancel]
    exact (normalizer (A : Set G)).one_mem
  · have hb2 : b ^ 2 = 1 := hp.A_exp b hb.1
    have hv2 : v ^ 2 = 1 := hp.V_exp v hv
    have hbi : b⁻¹ = b := inv_eq_self_of_sq_eq_one' hb2
    have hvi : v⁻¹ = v := inv_eq_self_of_sq_eq_one' hv2
    have hbb : b * b = 1 := by simpa [pow_two] using hb2
    have hbvb : b * v * b ∈ V := by
      have := (mem_normalizer_iff.mp hb.2 v).mp hv
      rw [hbi] at this
      exact this
    have hcomm : (b * v * b) * v = v * (b * v * b) := hp.V_comm _ hbvb v hv
    have e1 : b * v * b * v = v * b * v * b := by
      calc b * v * b * v = v * (b * v * b) := hcomm
        _ = v * b * v * b := by group
    have hc : (b⁻¹ * v * b * v⁻¹) * b = b * (b⁻¹ * v * b * v⁻¹) := by
      rw [hbi, hvi]
      calc (b * v * b * v) * b = (v * b * v * b) * b := by rw [e1]
        _ = v * b * v * (b * b) := by group
        _ = v * b * v := by rw [hbb, mul_one]
        _ = (b * b) * (v * b * v) := by rw [hbb, one_mul]
        _ = b * (b * v * b * v) := by group
    exact mem_normalizer_of_commute_of_TI hp.A_TI hb.1 hb1 hc

theorem card_le [Finite G] (hp : TIPair V A) {v : G} (hv : v ∈ V)
    (hvU : v ∉ normalizer (A : Set G)) :
    Nat.card ↥(A ⊓ normalizer (V : Set G)) ≤ Nat.card ↥(V ⊓ normalizer (A : Set G)) := by
  let f : ↥(A ⊓ normalizer (V : Set G)) → ↥(V ⊓ normalizer (A : Set G)) := fun b =>
    ⟨(b : G)⁻¹ * v * b * v⁻¹, hp.commutator_mem b.2 hv⟩
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨x, hx⟩ ⟨x', hx'⟩ hbb'
  have h1 : x⁻¹ * v * x * v⁻¹ = x'⁻¹ * v * x' * v⁻¹ := congrArg Subtype.val hbb'
  have h2 : x⁻¹ * v * x = x'⁻¹ * v * x' := mul_right_cancel h1
  have hdA : x * x'⁻¹ ∈ A := A.mul_mem hx.1 (A.inv_mem hx'.1)
  have hcomm : v * (x * x'⁻¹) = (x * x'⁻¹) * v := by
    calc v * (x * x'⁻¹) = x * (x⁻¹ * v * x) * x'⁻¹ := by group
      _ = x * (x'⁻¹ * v * x') * x'⁻¹ := by rw [h2]
      _ = (x * x'⁻¹) * v := by group
  by_cases hd1 : x * x'⁻¹ = 1
  · exact Subtype.ext (mul_inv_eq_one.mp hd1)
  · exact absurd (mem_normalizer_of_commute_of_TI hp.A_TI hdA hd1 hcomm) hvU

theorem card_lt_of_le_of_ne [Finite G] {X Y : Subgroup G} (h : X ≤ Y) (hne : X ≠ Y) :
    Nat.card X < Nat.card Y :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h) fun e =>
    hne (Subgroup.eq_of_le_of_card_ge h e.symm.le)

theorem commute_of_pGroup [Finite G] (hp : TIPair V A) (hX : IsPGroup 2 ↥(V ⊔ A))
    (hcard : Nat.card V = Nat.card A) (hU : V ⊓ normalizer (A : Set G) ≠ ⊥) :
    ∀ v ∈ V, ∀ a ∈ A, v * a = a * v := by
  classical
  have hUB : ∀ u ∈ V ⊓ normalizer (A : Set G), ∀ b ∈ A ⊓ normalizer (V : Set G), u * b = b * u :=
    fun u hu b hb => hp.commute_of_mem hu hb
  have hUV : V ⊓ normalizer (A : Set G) ≤ V := inf_le_left
  have hBA : A ⊓ normalizer (V : Set G) ≤ A := inf_le_left
  have hAbot : A ≠ ⊥ := by
    intro hA
    rw [hA, Subgroup.card_bot] at hcard
    have hV : V = ⊥ := Subgroup.card_eq_one.mp hcard
    exact hU (eq_bot_iff.mpr (inf_le_left.trans hV.le))
  have hB : A ⊓ normalizer (V : Set G) ≠ ⊥ := by
    obtain ⟨⟨u, hu⟩, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
    obtain ⟨a, ha, ha1, hc⟩ :=
      exists_commute_of_normalizer hp.A_comm hp.A_exp hAbot hu.2 (hp.V_exp u hu.1)
    have hn : a ∈ normalizer (V : Set G) :=
      mem_normalizer_of_commute_of_TI hp.V_TI hu.1 hu1 hc.symm
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨a, ha, hn⟩, fun h => ha1 (congrArg Subtype.val h)⟩
  have hBU : A ⊓ normalizer (V : Set G) ≤ normalizer ((V ⊓ normalizer (A : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_commute hUB
  have hYmem : ∀ y : G, y ∈ (V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) ↔
      ∃ n ∈ V ⊓ normalizer (A : Set G), ∃ h ∈ A ⊓ normalizer (V : Set G), y = n * h :=
    fun y => mem_sup_iff_of_le_normalizer hBU
  have hVY : V ≤ normalizer (((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) :
      Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun v hv y hy => ?_
    obtain ⟨u, hu, b, hb, rfl⟩ := (hYmem y).mp hy
    have hc' := hp.commutator_mem hb hv
    have hvu : v * u * v⁻¹ = u := by rw [hp.V_comm v hv u (hUV hu)]; group
    have hvb : v * b * v⁻¹ = b * (b⁻¹ * v * b * v⁻¹) := by group
    have hcb := hUB _ hc' b hb
    have e : v * (u * b) * v⁻¹ = (u * (b⁻¹ * v * b * v⁻¹)) * b := by
      calc v * (u * b) * v⁻¹ = (v * u * v⁻¹) * (v * b * v⁻¹) := by group
        _ = u * (b * (b⁻¹ * v * b * v⁻¹)) := by rw [hvu, hvb]
        _ = u * ((b⁻¹ * v * b * v⁻¹) * b) := by rw [hcb]
        _ = (u * (b⁻¹ * v * b * v⁻¹)) * b := (mul_assoc _ _ _).symm
    rw [e]
    exact Subgroup.mul_mem_sup ((V ⊓ normalizer (A : Set G)).mul_mem hu hc') hb
  have hAY : A ≤ normalizer (((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) :
      Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun a ha y hy => ?_
    obtain ⟨u, hu, b, hb, rfl⟩ := (hYmem y).mp hy
    have hc'' := hp.symm.commutator_mem hu ha
    have hab : a * b * a⁻¹ = b := by rw [hp.A_comm a ha b (hBA hb)]; group
    have hau : a * u * a⁻¹ = u * (u⁻¹ * a * u * a⁻¹) := by group
    have e : a * (u * b) * a⁻¹ = u * ((u⁻¹ * a * u * a⁻¹) * b) := by
      calc a * (u * b) * a⁻¹ = (a * u * a⁻¹) * (a * b * a⁻¹) := by group
        _ = u * (u⁻¹ * a * u * a⁻¹) * b := by rw [hau, hab]
        _ = u * ((u⁻¹ * a * u * a⁻¹) * b) := by rw [mul_assoc]
    rw [e]
    exact Subgroup.mul_mem_sup hu ((A ⊓ normalizer (V : Set G)).mul_mem hc'' hb)
  have hYX : (V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) ≤ V ⊔ A :=
    sup_le (hUV.trans le_sup_left) (hBA.trans le_sup_right)
  have hXY : V ⊔ A ≤ normalizer (((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) :
      Subgroup G) : Set G) := sup_le hVY hAY
  have hYne : (V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) ≠ ⊥ := fun h =>
    hU (eq_bot_iff.mpr (le_sup_left.trans h.le))
  obtain ⟨z, hzY, hz1, hzc⟩ := exists_mem_inf_center_of_normal hX hYX hXY hYne
  obtain ⟨u, hu, b, hb, rfl⟩ := (hYmem z).mp hzY
  have hzV : ∀ v ∈ V, v * (u * b) = (u * b) * v := fun v hv =>
    Subgroup.mem_centralizer_iff.mp hzc v (Subgroup.mem_sup_left hv)
  have hzA : ∀ a ∈ A, a * (u * b) = (u * b) * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp hzc a (Subgroup.mem_sup_right ha)
  have hcases : A ≤ A ⊓ normalizer (V : Set G) ∨ V ≤ V ⊓ normalizer (A : Set G) := by
    by_cases hb1 : b = 1
    · left
      have hu1 : u ≠ 1 := fun h => hz1 (by rw [h, hb1, mul_one])
      intro a ha
      refine ⟨ha, mem_normalizer_of_commute_of_TI hp.V_TI hu.1 hu1 ?_⟩
      have := hzA a ha
      rwa [hb1, mul_one] at this
    · right
      intro v hv
      refine ⟨hv, mem_normalizer_of_commute_of_TI hp.A_TI hb.1 hb1 ?_⟩
      have h1 := hzV v hv
      have h2 : u * (v * b) = u * (b * v) := by
        calc u * (v * b) = (u * v) * b := by rw [mul_assoc]
          _ = (v * u) * b := by rw [hp.V_comm u hu.1 v hv]
          _ = v * (u * b) := by rw [mul_assoc]
          _ = (u * b) * v := h1
          _ = u * (b * v) := by rw [mul_assoc]
      exact mul_left_cancel h2
  have hboth : V ≤ V ⊓ normalizer (A : Set G) ∧ A ≤ A ⊓ normalizer (V : Set G) := by
    rcases hcases with hAB | hVU
    · refine ⟨?_, hAB⟩
      by_contra hnot
      obtain ⟨v, hv, hvU⟩ : ∃ v ∈ V, v ∉ V ⊓ normalizer (A : Set G) := by
        by_contra hcon
        exact hnot fun v hv => by_contra fun hvU => hcon ⟨v, hv, hvU⟩
      have hvN : v ∉ normalizer (A : Set G) := fun h => hvU ⟨hv, h⟩
      have h1 := hp.card_le hv hvN
      have hBeq : A ⊓ normalizer (V : Set G) = A := le_antisymm hBA hAB
      rw [hBeq, ← hcard] at h1
      have h2 : Nat.card ↥(V ⊓ normalizer (A : Set G)) < Nat.card V :=
        card_lt_of_le_of_ne hUV (fun e => hvU (by rw [e]; exact hv))
      omega
    · refine ⟨hVU, ?_⟩
      by_contra hnot
      obtain ⟨a, ha, haB⟩ : ∃ a ∈ A, a ∉ A ⊓ normalizer (V : Set G) := by
        by_contra hcon
        exact hnot fun a ha => by_contra fun haB => hcon ⟨a, ha, haB⟩
      have haN : a ∉ normalizer (V : Set G) := fun h => haB ⟨ha, h⟩
      have h1 := hp.symm.card_le ha haN
      have hUeq : V ⊓ normalizer (A : Set G) = V := le_antisymm hUV hVU
      rw [hUeq, hcard] at h1
      have h2 : Nat.card ↥(A ⊓ normalizer (V : Set G)) < Nat.card A :=
        card_lt_of_le_of_ne hBA (fun e => haB (by rw [e]; exact ha))
      omega
  intro v hv a ha
  exact hUB v (hboth.1 hv) a (hboth.2 ha)

end TIPair

theorem comm_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (h : IsElemAbelian p E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm h ha hb

theorem tiAbelianTwoGroupCommute : TIAbelianTwoGroupCommute := by
  intro G _ _ V A hVe hAe hcard hVTI hATI hAV hX hU
  have key : ∀ v ∈ V, ∀ a ∈ A, v * a = a * v := by
    by_cases hVA : A = V
    · subst hVA
      intro v hv a ha
      exact comm_of_isElemAbelian hAe hv ha
    · have h1 : conjR A (1 : G) = A := conjR_eq_of_mem A.one_mem
      have h2 := hAV 1 (by rw [h1]; exact hVA)
      rw [h1] at h2
      have hinf : V ⊓ A = ⊥ := by rw [inf_comm]; exact h2
      exact TIPair.commute_of_pGroup
        ⟨fun a ha b hb => comm_of_isElemAbelian hVe ha hb, hVe.2,
          fun a ha b hb => comm_of_isElemAbelian hAe ha hb, hAe.2, hVTI, hATI, hinf⟩ hX hcard hU
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.mpr fun v hv a ha => ?_
  exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (key v hv a ha))

end CFSG.QuasithinUnique.Lin2

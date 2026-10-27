module

public import CFSG.Certificates.Kernel.SporLatDcPair
public import CFSG.Certificates.Kernel.SporLatOmegaSound

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open MulAction

@[ext] structure PtL (m : ℕ) where
  val : List ℕ
  valid : PtValid m val

instance (m : ℕ) : DecidableEq (PtL m) := fun a b =>
  decidable_of_iff (a.val = b.val) PtL.ext_iff.symm

variable {Γ : Type} [Group Γ]

instance (m : ℕ) [MulAction Γ (Fin m)] : MulAction Γ (PtL m) where
  smul g L := ⟨ptAct (tab m g).toArray L.val, ptLab_lawful.valid_act g L.valid⟩
  one_smul L := PtL.ext (ptLab_lawful.act_one L.valid)
  mul_smul g h L := PtL.ext (ptLab_lawful.act_mul g h L.valid)

section Pt

variable {m : ℕ} [MulAction Γ (Fin m)]

theorem smul_val (g : Γ) (L : PtL m) : (g • L).val = ptAct (tab m g).toArray L.val := rfl

theorem smul_val_eq {g : Γ} {f : ℕ → ℕ} (hg : Good m (tab m g).toArray f) (L : PtL m) :
    (g • L).val = SLDc.labF f L.val :=
  CFSG.KC.SLOm.ptAct_good hg L.valid.2

theorem mem_smul_val {g : Γ} {L : PtL m} {p : ℕ} :
    p ∈ (g • L).val ↔ ∃ q ∈ L.val, act m g q = p := by
  rw [smul_val, ptAct_tab, mem_sortN, List.mem_map]

theorem act_inj {g : Γ} {p q : ℕ} (hp : p < m) (hq : q < m) (h : act m g p = act m g q) :
    p = q := by
  have e1 : act m g p = (g • (⟨p, hp⟩ : Fin m)).val := act_eq g ⟨p, hp⟩
  have e2 : act m g q = (g • (⟨q, hq⟩ : Fin m)).val := act_eq g ⟨q, hq⟩
  rw [e1, e2] at h
  exact congrArg Fin.val (smul_left_cancel g (Fin.ext h))

theorem nodup_smul {g : Γ} {L : PtL m} (h : L.val.Nodup) : (g • L).val.Nodup := by
  rw [smul_val, ptAct_tab]
  exact (sortN_perm _).nodup_iff.2
    (List.Nodup.map_on (fun p hp q hq e => act_inj (L.valid.2 p hp) (L.valid.2 q hq) e) h)

theorem act_val {g : Γ} {p : ℕ} (hp : p < m) : (g • (⟨p, hp⟩ : Fin m)).val = act m g p :=
  (act_eq g ⟨p, hp⟩).symm

end Pt

@[ext] structure PrL (n : ℕ) where
  val : List ℕ
  valid : PtValid (n * n) val

instance (n : ℕ) [MulAction Γ (Fin n)] : MulAction Γ (PrL n) :=
  letI : MulAction Γ (Fin (n * n)) := SLDc.pairAction Γ n
  { smul := fun g L => ⟨ptAct (tab (n * n) g).toArray L.val, ptLab_lawful.valid_act g L.valid⟩
    one_smul := fun L => PrL.ext (ptLab_lawful.act_one L.valid)
    mul_smul := fun g h L => PrL.ext (ptLab_lawful.act_mul g h L.valid) }

theorem prSmul_val_eq {n : ℕ} [MulAction Γ (Fin n)] {g : Γ} {f : ℕ → ℕ}
    (hg : Good n (tab n g).toArray f) (L : PrL n) :
    (g • L).val = SLDc.labF (SLDc.pairF n f) L.val :=
  CFSG.KC.SLOm.ptAct_good (SLDc.good_pair hg) L.valid.2

theorem card_eq_ncard_mul {α : Type*} [MulAction Γ α] (K : Subgroup Γ) (a : α) :
    Nat.card K = (orbit K a).ncard * Nat.card (stabilizer K a) := by
  rw [← index_stabilizer K a, mul_comm]
  exact (Subgroup.card_mul_index (stabilizer K a)).symm

theorem card_stabilizer_eq {α : Type*} [MulAction Γ α] (K : Subgroup Γ) (a : α) :
    Nat.card (stabilizer K a) = Nat.card (stabilizer Γ a ⊓ K : Subgroup Γ) := by
  rw [← stabilizer_subgroupOf, ← Subgroup.subgroupOf_map_subtype]
  exact (Subgroup.card_map_of_injective K.subtype_injective).symm

theorem smul_mem_of_closure [Finite Γ] {α : Type*} [MulAction Γ α] {E : Set Γ} {F : Set α}
    (hF : ∀ e ∈ E, ∀ y ∈ F, e • y ∈ F) {k : Γ} (hk : k ∈ Subgroup.closure E) :
    ∀ y ∈ F, k • y ∈ F := by
  have hk' : k ∈ Submonoid.closure E := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hk
  clear hk
  induction hk' using Submonoid.closure_induction with
  | mem e he => exact hF e he
  | one => intro y hy; rwa [one_smul]
  | mul a b _ _ ha hb => intro y hy; rw [mul_smul]; exact ha _ (hb y hy)

theorem three_dvd_orderOf {m : ℕ} [MulAction Γ (Fin m)] (w : Γ) (p : Fin m) {l : ℕ}
    (hl : 3 ∣ l) (h1 : w ^ l • p = p) (h2 : w ^ (l / 3) • p ≠ p) : 3 ∣ orderOf w := by
  have hper : ∀ e, Function.IsPeriodicPt (w • ·) e p ↔ w ^ e • p = p := fun e => by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate]
  have hd1 := ((hper l).2 h1).minimalPeriod_dvd
  have hd2 : ¬ Function.minimalPeriod (w • ·) p ∣ l / 3 := fun h =>
    h2 ((hper _).1 (Function.isPeriodicPt_iff_minimalPeriod_dvd.2 h))
  have hd3 := ((hper (orderOf w)).2 (by rw [pow_orderOf_eq_one, one_smul])).minimalPeriod_dvd
  refine Nat.dvd_trans ?_ hd3
  by_contra h3
  have hc : Nat.Coprime (Function.minimalPeriod (w • ·) p) 3 :=
    Nat.coprime_comm.1 (Nat.prime_three.coprime_iff_not_dvd.2 h3)
  obtain ⟨t, rfl⟩ := hl
  rw [Nat.mul_div_cancel_left t (by norm_num)] at hd2
  exact hd2 (hc.dvd_of_dvd_mul_left hd1)

end CFSG.KC.SLD2

end

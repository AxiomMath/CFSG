module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Coord
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

open CFSG.LocalCores CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp mem_cjComp_iff mem_cjComp_of_mem)

section CentralPart

variable {Y : Type*} [Group Y]

@[expose] def centralPart (K : ComponentIndex Y) (U : Subgroup Y) : Subgroup Y :=
  U ⊓ (center K.1).map K.1.subtype

theorem mem_centralPart_iff {K : ComponentIndex Y} {U : Subgroup Y} {g : Y} :
    g ∈ centralPart K U ↔ g ∈ U ∧ g ∈ K.1 ∧ g ∈ centralizer (K.1 : Set Y) := by
  rw [centralPart, mem_inf, mem_map_center_iff]

theorem centralPart_le (K : ComponentIndex Y) (U : Subgroup Y) : centralPart K U ≤ U :=
  inf_le_left

end CentralPart

section Conjugate

variable {Y : Type*} [Group Y] [Finite Y]

theorem centralPart_cjComp (g : Y) (K : ComponentIndex Y) (U : Subgroup Y) :
    centralPart (cjComp g K) (U.map (MulAut.conj g).toMonoidHom) =
      (centralPart K U).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_centralPart_iff, mem_map]
  constructor
  · rintro ⟨hxU, hxK, hxc⟩
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hxU
    refine ⟨u, mem_centralPart_iff.mpr ⟨hu, ?_, ?_⟩, rfl⟩
    · have h := (mem_cjComp_iff g K).mp hxK
      simpa [mul_assoc] using h
    · rw [mem_centralizer_iff]
      intro k hk
      have h := mem_centralizer_iff.mp hxc (g * k * g⁻¹) (mem_cjComp_of_mem g K hk)
      have h' : g * (k * u) * g⁻¹ = g * (u * k) * g⁻¹ := by
        calc g * (k * u) * g⁻¹ = g * k * g⁻¹ * (g * u * g⁻¹) := by group
          _ = g * u * g⁻¹ * (g * k * g⁻¹) := h
          _ = g * (u * k) * g⁻¹ := by group
      simpa using h'
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyU, hyK, hyc⟩ := mem_centralPart_iff.mp hy
    refine ⟨mem_map_of_mem _ hyU, mem_cjComp_of_mem g K hyK, ?_⟩
    rw [mem_centralizer_iff]
    intro m hm
    have h := mem_centralizer_iff.mp hyc (g⁻¹ * m * g) ((mem_cjComp_iff g K).mp hm)
    have h' : g * (g⁻¹ * m * g * y) * g⁻¹ = g * (y * (g⁻¹ * m * g)) * g⁻¹ := by rw [h]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc m * (g * y * g⁻¹) = g * (g⁻¹ * m * g * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * m * g)) * g⁻¹ := h'
      _ = g * y * g⁻¹ * m := by group

theorem card_centralPart_cjComp (g : Y) (K : ComponentIndex Y) (U : Subgroup Y) :
    Nat.card (centralPart (cjComp g K) (U.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (centralPart K U) := by
  rw [centralPart_cjComp]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end Conjugate

namespace Count

section Join

variable {Y : Type*} [Group Y] [Finite Y] {ι : Type*} [Fintype ι]
  (K : ι → ComponentIndex Y) (U : ι → Subgroup Y)

theorem pairwise_commute (hK : Function.Injective K) (hU : ∀ i, U i ≤ (K i).1) :
    Pairwise fun i j : ι => ∀ x y : Y, x ∈ U i → y ∈ U j → Commute x y :=
  fun _ _ hij x y hx hy => componentIndex_commute (hK.ne hij) x y (hU _ hx) (hU _ hy)

@[expose] noncomputable def joinMul (hK : Function.Injective K) (hU : ∀ i, U i ≤ (K i).1) :
    (∀ i, U i) →* Y :=
  Subgroup.noncommPiCoprod (pairwise_commute K U hK hU)

theorem joinMul_range (hK : Function.Injective K) (hU : ∀ i, U i ≤ (K i).1) :
    (joinMul K U hK hU).range = ⨆ i, U i :=
  Subgroup.noncommPiCoprod_range

theorem joinMul_apply (hK : Function.Injective K) (hU : ∀ i, U i ≤ (K i).1) (u : ∀ i, U i) :
    joinMul K U hK hU u = Finset.univ.noncommProd (fun i => (u i : Y))
      (fun i _ j _ h => pairwise_commute K U hK hU h _ _ (u i).2 (u j).2) :=
  Subgroup.noncommPiCoprod_apply _ u

@[simp]
theorem joinMul_mulSingle [DecidableEq ι] (hK : Function.Injective K)
    (hU : ∀ i, U i ≤ (K i).1) (i : ι) (y : U i) :
    joinMul K U hK hU (Pi.mulSingle i y) = (y : Y) :=
  Subgroup.noncommPiCoprod_mulSingle i y

theorem joinMul_mem (hK : Function.Injective K) (hU : ∀ i, U i ≤ (K i).1) {H : Subgroup Y}
    (u : ∀ i, U i) (hu : ∀ i, (u i : Y) ∈ H) : joinMul K U hK hU u ∈ H := by
  rw [joinMul_apply]
  exact noncommProd_mem H _ fun i _ => hu i

theorem joinMul_eq_mul_update [DecidableEq ι] (hK : Function.Injective K)
    (hU : ∀ i, U i ≤ (K i).1) (u : ∀ i, U i) (j : ι) :
    joinMul K U hK hU u = (u j : Y) * joinMul K U hK hU (Function.update u j 1) := by
  have hx : Pi.mulSingle j (u j) * Function.update u j 1 = u := by
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]
  calc joinMul K U hK hU u
      = joinMul K U hK hU (Pi.mulSingle j (u j) * Function.update u j 1) := by rw [hx]
    _ = _ := by rw [map_mul, joinMul_mulSingle]

theorem commute_joinMul_update [DecidableEq ι] (hK : Function.Injective K)
    (hU : ∀ i, U i ≤ (K i).1) (u : ∀ i, U i) (j : ι) {k : Y} (hk : k ∈ (K j).1) :
    Commute k (joinMul K U hK hU (Function.update u j 1)) := by
  have h : joinMul K U hK hU (Function.update u j 1) ∈ centralizer {k} := by
    refine joinMul_mem K U hK hU _ fun i => ?_
    by_cases hi : i = j
    · subst hi
      simp
    · rw [Function.update_of_ne hi, mem_centralizer_singleton_iff]
      exact componentIndex_commute (hK.ne hi) _ _ (hU i (u i).2) hk
  exact (mem_centralizer_singleton_iff.mp h).symm

theorem commute_joinMul_iff [DecidableEq ι] (hK : Function.Injective K)
    (hU : ∀ i, U i ≤ (K i).1) (u : ∀ i, U i) (j : ι) {k : Y} (hk : k ∈ (K j).1) :
    Commute k (joinMul K U hK hU u) ↔ Commute k (u j : Y) := by
  have hu := commute_joinMul_update K U hK hU u j hk
  rw [joinMul_eq_mul_update K U hK hU u j]
  refine ⟨fun h => ?_, fun h => h.mul_right hu⟩
  have := h.mul_right hu.inv_right
  rwa [mul_inv_cancel_right] at this

@[expose] def centralPi : Subgroup (∀ i, U i) :=
  Subgroup.pi Set.univ fun i => (centralPart (K i) (U i)).subgroupOf (U i)

theorem mem_centralPi_iff {u : ∀ i, U i} :
    u ∈ centralPi K U ↔ ∀ i, (u i : Y) ∈ centralPart (K i) (U i) := by
  simp [centralPi, Subgroup.mem_pi, mem_subgroupOf]

theorem card_centralPi :
    Nat.card (centralPi K U) = ∏ i, Nat.card (centralPart (K i) (U i)) := by
  have h : Nat.card (centralPi K U) =
      Nat.card (∀ i, (centralPart (K i) (U i)).subgroupOf (U i)) :=
    Nat.card_congr
      { toFun := fun x i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
        invFun := fun y => ⟨fun i => y i, fun i _ => (y i).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h, Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (centralPart_le (K i) (U i))).toEquiv

theorem ker_joinMul_le [DecidableEq ι] (hK : Function.Injective K) (hU : ∀ i, U i ≤ (K i).1) :
    (joinMul K U hK hU).ker ≤ centralPi K U := by
  intro u hu
  rw [mem_centralPi_iff]
  intro i
  rw [mem_centralPart_iff]
  refine ⟨(u i).2, hU i (u i).2, ?_⟩
  rw [mem_centralizer_iff]
  intro k hk
  have h : Commute k (joinMul K U hK hU u) := by
    rw [MonoidHom.mem_ker.mp hu]
    exact Commute.one_right k
  exact ((commute_joinMul_iff K U hK hU u i hk).mp h).eq

variable {p : ℕ}

theorem pi_mul_comm (hUe : ∀ i, IsElemAbelian p (U i)) (u v : ∀ i, U i) : u * v = v * u := by
  funext i
  haveI := (hUe i).1
  exact mul_comm' (u i) (v i)

theorem pi_pow_eq_one (hUe : ∀ i, IsElemAbelian p (U i)) (u : ∀ i, U i) : u ^ p = 1 := by
  funext i
  apply Subtype.ext
  simpa using (hUe i).2 (u i : Y) (u i).2

theorem isPGroup_pi (hUe : ∀ i, IsElemAbelian p (U i)) : IsPGroup p (∀ i, U i) :=
  fun u => ⟨1, by simpa using pi_pow_eq_one U hUe u⟩

theorem isElemAbelian_iSup (hK : Function.Injective K) (hU : ∀ i, U i ≤ (K i).1)
    (hUe : ∀ i, IsElemAbelian p (U i)) : IsElemAbelian p (⨆ i, U i) := by
  rw [← joinMul_range K U hK hU]
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨u, hu⟩ := a.2
    obtain ⟨v, hv⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hu, ← hv, ← map_mul, ← map_mul, pi_mul_comm U hUe u v]
  · obtain ⟨u, rfl⟩ := hx
    rw [← map_pow, pi_pow_eq_one U hUe u, map_one]

theorem prod_card_eq (hK : Function.Injective K) (hU : ∀ i, U i ≤ (K i).1) :
    ∏ i, Nat.card (U i) =
      Nat.card (⨆ i, U i : Subgroup Y) * Nat.card (joinMul K U hK hU).ker := by
  rw [← Nat.card_pi, ← joinMul_range K U hK hU, mul_comm]
  exact (Subgroup.card_ker_mul_card_range _).symm

end Join

end Count

section Main

open Count

theorem card_iSup_components {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {ι : Type*} [Fintype ι] (K : ι → ComponentIndex Y) (hK : Function.Injective K)
    (U : ι → Subgroup Y) (hU : ∀ i, U i ≤ (K i).1) (hUe : ∀ i, IsElemAbelian p (U i)) :
    IsElemAbelian p (⨆ i, U i) ∧
      (∏ i, Nat.card (U i)) ≤
        Nat.card (⨆ i, U i : Subgroup Y) * ∏ i, Nat.card (centralPart (K i) (U i)) ∧
      ((∃ j, centralPart (K j) (U j) ≠ ⊥) →
        p * ∏ i, Nat.card (U i) ≤
          Nat.card (⨆ i, U i : Subgroup Y) * ∏ i, Nat.card (centralPart (K i) (U i))) := by
  classical
  have hker := ker_joinMul_le K U hK hU
  have hA := prod_card_eq K U hK hU
  have hN := card_centralPi K U
  refine ⟨isElemAbelian_iSup K U hK hU hUe, ?_, ?_⟩
  · rw [hA, ← hN]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hker)
  · rintro ⟨j, hj⟩
    obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hj
    have hcU : (c : Y) ∈ U j := (mem_centralPart_iff.mp c.2).1
    have hv : (Pi.mulSingle j (⟨c, hcU⟩ : U j) : ∀ i, U i) ∈ centralPi K U := by
      rw [mem_centralPi_iff]
      intro i
      by_cases hi : i = j
      · subst hi
        simpa using c.2
      · simp [Pi.mulSingle_eq_of_ne hi, one_mem]
    have hv' : (Pi.mulSingle j (⟨c, hcU⟩ : U j) : ∀ i, U i) ∉ (joinMul K U hK hU).ker := by
      rw [MonoidHom.mem_ker, joinMul_mulSingle]
      exact fun h => hc (Subtype.ext h)
    have hlt : (joinMul K U hK hU).ker < centralPi K U :=
      lt_of_le_of_ne hker fun h => hv' (h ▸ hv)
    haveI : Fact p.Prime := ⟨hp⟩
    have hP := isPGroup_pi U hUe
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hP.to_subgroup (joinMul K U hK hU).ker)
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hP.to_subgroup (centralPi K U))
    have hcard := Subgroup.card_lt_of_lt hlt
    rw [ha, hb] at hcard
    have hab : a < b := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcard
    have hpk : p * Nat.card (joinMul K U hK hU).ker ≤ Nat.card (centralPi K U) := by
      rw [ha, hb, ← pow_succ']
      exact Nat.pow_le_pow_right hp.pos hab
    rw [hA, ← hN]
    calc p * (Nat.card (⨆ i, U i : Subgroup Y) * Nat.card (joinMul K U hK hU).ker)
        = Nat.card (⨆ i, U i : Subgroup Y) * (p * Nat.card (joinMul K U hK hU).ker) := by ring
      _ ≤ Nat.card (⨆ i, U i : Subgroup Y) * Nat.card (centralPi K U) :=
        Nat.mul_le_mul_left _ hpk

end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

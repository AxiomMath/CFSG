
module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeModelBase1

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeModelBase

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Fischer CFSG.ComponentClassification.M12Cover
open scoped Pointwise

theorem letter_eq
    (k : ℕ) (hk : k < 46) : letter k hk = t46G ((k : ℤ) + 1) :=
  rep_unique (rep_letter k hk) (rep_t46G _)

theorem letter_mem
    (k : ℕ) (hk : k < 46) : letter k hk ∈ T46 := by
  rw [letter_eq]
  exact t46G_mem _

theorem u62Letters_mem :
    ∀ g ∈ u62Letters, g ∈ T46 := by
  intro g hg
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
  exact letter_mem k k.2

theorem u62W_mem
    (w : List ℤ) : u62W w ∈ T46 := by
  rw [u62W, tab_eq]
  exact evalCodes_mem _ u62Letters_mem w

theorem map_u62W_mem
    (ws : List (List ℤ)) : ∀ g ∈ ws.map u62W, g ∈ T46 := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact u62W_mem w

abbrev uA : Subgroup (Equiv.Perm (Fin 693)) := aQ.originalSubgroup

abbrev uK : Subgroup (Equiv.Perm (Fin 693)) := kQ.originalSubgroup

abbrev uP : Subgroup (Equiv.Perm (Fin 693)) := pQ.originalSubgroup

abbrev uS : Subgroup (Equiv.Perm (Fin 693)) := sQ.originalSubgroup

abbrev uT : Subgroup (Equiv.Perm (Fin 693)) := tQ.originalSubgroup

theorem uA_eq : uA = Subgroup.closure {g | g ∈ aGens} := by
  rw [uA, aQ, certificate_originalSubgroup]

theorem uK_eq : uK = Subgroup.closure {g | g ∈ kGens} := by
  rw [uK, kQ, certificate_originalSubgroup]

theorem uP_closure : uP = Subgroup.closure {g | g ∈ pGens} := by
  rw [uP, pQ, certificate_originalSubgroup]

theorem uS_closure : uS = Subgroup.closure {g | g ∈ sGens} := by
  rw [uS, sQ, certificate_originalSubgroup]

theorem uT_eq : uT = Subgroup.closure {g | g ∈ tGens} := by
  rw [uT, tQ, certificate_originalSubgroup]

theorem aGens_mem : ∀ g ∈ aGens, g ∈ uA := fun g hg => by
  rw [uA_eq]
  exact Subgroup.subset_closure hg

theorem kGens_mem : ∀ g ∈ kGens, g ∈ uK := fun g hg => by
  rw [uK_eq]
  exact Subgroup.subset_closure hg

theorem sGens_mem : ∀ g ∈ sGens, g ∈ uS := fun g hg => by
  rw [uS_closure]
  exact Subgroup.subset_closure hg

theorem tGens_mem : ∀ g ∈ tGens, g ∈ uT := fun g hg => by
  rw [uT_eq]
  exact Subgroup.subset_closure hg

theorem uA_le_T46 :
    uA ≤ T46 := by
  rw [uA_eq]
  exact closure_le_of_mem (map_u62W_mem _)

theorem uK_le_T46 :
    uK ≤ T46 := by
  rw [uK_eq]
  exact closure_le_of_mem (map_u62W_mem _)

theorem uT_le_T46 :
    uT ≤ T46 := by
  rw [uT_eq]
  exact closure_le_of_mem (map_u62W_mem _)

theorem uS_le_T46 :
    uS ≤ T46 := by
  rw [uS_closure]
  refine closure_le_of_mem fun g hg => ?_
  rcases List.mem_append.1 hg with hg | hg
  · exact map_u62W_mem _ g hg
  · exact map_u62W_mem _ g hg

theorem uP_eq : uP = uA ⊔ uK := by
  rw [uP_closure, uA_eq, uK_eq, ← Subgroup.closure_union]
  congr 1
  ext g
  simp [pGens]

theorem uS_eq : uS = uA ⊔ uT := by
  rw [uS_closure, uA_eq, uT_eq, ← Subgroup.closure_union]
  congr 1
  ext g
  simp [sGens]

theorem uA_le_uS : uA ≤ uS := by
  rw [uS_eq]
  exact le_sup_left

theorem uP_le_T46 :
    uP ≤ T46 := by
  rw [uP_eq]
  exact sup_le uA_le_T46 uK_le_T46

theorem j3_mem : j3 ∈ uA := evalCodes_mem _ aGens_mem _

theorem j1_mem : j1 ∈ uA := evalCodes_mem _ aGens_mem _

theorem j2_mem : j2 ∈ uA := evalCodes_mem _ aGens_mem _

theorem uA_fix
    : ∀ a ∈ uA, ∀ p ∈ finSet 693 fixA, a p = p := by
  intro a ha p hp
  have ha' := ha
  rw [uA_eq] at ha'
  induction ha' using Subgroup.closure_induction with
  | mem y hy => exact fix_check.2.1 y hy p hp
  | one => rfl
  | mul y z _ _ ihy ihz =>
    rw [Equiv.Perm.mul_apply, ihz (by assumption), ihy (by assumption)]
  | inv y _ ihy =>
    rw [Equiv.Perm.inv_eq_iff_eq, ihy (by assumption)]

open CFSG.ComponentClassification.PSL3Four in
theorem kGens_getD_mem
    {m : ℕ} (hm : m < 3) : kGens.getD m 1 ∈ uK := by
  apply kGens_mem
  rw [List.getD_eq_getElem _ _ (by simpa [kGens, kWords] using hm)]
  exact List.getElem_mem _

theorem chains_facts :
    ValidSchreier aQ ∧ aQ.orderCertificate = 512 ∧ ValidSchreier kQ ∧
      kQ.orderCertificate = 20160 ∧ ValidSchreier pQ ∧ pQ.orderCertificate = 10321920 ∧
      ValidSchreier sQ ∧ sQ.orderCertificate = 32768 ∧ ValidSchreier tQ ∧
      tQ.orderCertificate = 64 := by
  have h := chains_check
  simp only [chainsCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem aQ_valid
    : ValidSchreier aQ := chains_facts.1
theorem kQ_valid
    : ValidSchreier kQ := chains_facts.2.2.1
theorem pQ_valid
    : ValidSchreier pQ := chains_facts.2.2.2.2.1
theorem sQ_valid
    : ValidSchreier sQ := chains_facts.2.2.2.2.2.2.1
theorem card_uA
    : Nat.card uA = 512 := by
  rw [← aQ.orderCertificate_eq_card aQ_valid, chains_facts.2.1]

theorem card_uK
    : Nat.card uK = 20160 := by
  rw [← kQ.orderCertificate_eq_card kQ_valid, chains_facts.2.2.2.1]

theorem card_uP
    : Nat.card uP = 10321920 := by
  rw [← pQ.orderCertificate_eq_card pQ_valid, chains_facts.2.2.2.2.2.1]

theorem card_uS
    : Nat.card uS = 32768 := by
  rw [← sQ.orderCertificate_eq_card sQ_valid, chains_facts.2.2.2.2.2.2.2.1]

theorem structure_facts :
    (∀ x ∈ aGens, orderOf x = 2 ∧ ∀ y ∈ aGens, x * y = y * x) ∧
      (∀ k ∈ kGens ++ tGens, ∀ a ∈ aGens, k * a * k⁻¹ ∈ uA) ∧ ∀ g ∈ tGens, g ∈ uK := by
  rw [uA_eq, uK_eq]
  exact structure_check

theorem uA_comm_gens
    : ∀ x ∈ uA, ∀ y ∈ aGens, x * y = y * x := by
  have hle : uA ≤ Subgroup.centralizer {g | g ∈ aGens} := by
    rw [uA_eq, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (structure_facts.1 x hx).2 y hy |>.symm
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) y hy).symm

theorem uA_comm
    : ∀ x ∈ uA, ∀ y ∈ uA, x * y = y * x := by
  intro x hx
  have hle : uA ≤ Subgroup.centralizer {x} := by
    rw [uA_eq, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (uA_comm_gens x hx y hy).symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem uA_sq
    : ∀ x ∈ uA, x ^ 2 = 1 := by
  intro x hx
  have hx' := hx
  rw [uA_eq] at hx'
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    rw [← (structure_facts.1 y hy).1]
    exact pow_orderOf_eq_one y
  | one => exact one_pow 2
  | mul y z hy hz ihy ihz =>
    have hy' : y ∈ uA := by rw [uA_eq]; exact hy
    have hz' : z ∈ uA := by rw [uA_eq]; exact hz
    rw [(Commute.mul_pow (uA_comm y hy' z hz') 2), ihy hy', ihz hz', one_mul]
  | inv y hy ihy =>
    have hy' : y ∈ uA := by rw [uA_eq]; exact hy
    rw [inv_pow, ihy hy', inv_one]

theorem uK_le_normalizer
    : uK ≤ Subgroup.normalizer (uA : Set (Equiv.Perm (Fin 693))) := by
  rw [uK_eq, Subgroup.closure_le]
  intro k hk
  exact mem_normalizer_of_conj_gens uA_eq fun a ha =>
    structure_facts.2.1 k (List.mem_append_left _ hk) a ha

theorem uT_le_normalizer
    : uT ≤ Subgroup.normalizer (uA : Set (Equiv.Perm (Fin 693))) := by
  rw [uT_eq, Subgroup.closure_le]
  intro k hk
  exact mem_normalizer_of_conj_gens uA_eq fun a ha =>
    structure_facts.2.1 k (List.mem_append_right _ hk) a ha

theorem uT_le_uK : uT ≤ uK := by
  rw [uT_eq]
  exact closure_le_of_mem structure_facts.2.2

theorem uP_le_normalizer
    : uP ≤ Subgroup.normalizer (uA : Set (Equiv.Perm (Fin 693))) := by
  rw [uP_eq]
  exact sup_le Subgroup.le_normalizer uK_le_normalizer

theorem eq_one_of_comm_aGens
    {k : Equiv.Perm (Fin 693)} (hk : k ∈ uK)
    (hc : ∀ a ∈ aGens, k * a = a * k) : k = 1 := by
  rw [uK_eq] at hk
  exact orbit_check.2.2.2.2.2.2.2.2.2.2 k hk hc

theorem uA_inf_uK : uA ⊓ uK = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact (Subgroup.mem_bot).2 (eq_one_of_comm_aGens hx.2 fun a ha =>
    (uA_comm_gens x hx.1 a ha))

theorem uA_inf_uT : uA ⊓ uT = ⊥ := by
  rw [eq_bot_iff, ← uA_inf_uK]
  exact inf_le_inf_left _ uT_le_uK

theorem fixed_j3
    : {p : Fin 693 | j3 p = p} = finSet 693 fixA := fix_check.1

theorem fix_uA
    : {p : Fin 693 | ∀ a ∈ uA, a p = p} = {p | j3 p = p} := by
  ext p
  constructor
  · intro hp
    exact hp j3 j3_mem
  · intro hp a ha
    rw [fixed_j3] at hp
    exact uA_fix a ha p hp

theorem smul_fixed_j3
    {g : Equiv.Perm (Fin 693)}
    (hg : g ∈ Subgroup.normalizer (uA : Set (Equiv.Perm (Fin 693)))) :
    g • {p : Fin 693 | j3 p = p} = {p | j3 p = p} := by
  have hsub : ∀ {h : Equiv.Perm (Fin 693)},
      h ∈ Subgroup.normalizer (uA : Set (Equiv.Perm (Fin 693))) →
      h • {p : Fin 693 | j3 p = p} ⊆ {p | j3 p = p} := by
    intro h hh
    rw [← fix_uA]
    rintro _ ⟨p, hp, rfl⟩ a ha
    have ha' : h⁻¹ * a * h⁻¹⁻¹ ∈ uA := (Subgroup.mem_normalizer_iff.1 (inv_mem hh) a).1 ha
    have hfix := hp _ ha'
    rw [inv_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hfix
    show a (h • p) = h • p
    rw [Equiv.Perm.smul_def]
    calc a (h p) = h (h⁻¹ (a (h p))) := (perm_apply_inv_self h _).symm
      _ = h p := by rw [hfix]
  exact Set.Subset.antisymm (hsub hg) (Set.subset_smul_set_iff.2 (hsub (inv_mem hg)))

theorem orbit_fixed_j3
    : 891 ≤ (Set.range fun g : T46 => g • {p : Fin 693 | j3 p = p}).ncard := by
  rw [fixed_j3]
  refine fix_check.2.2.trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨g, closure_le_of_mem u62Letters_mem g.2⟩, rfl⟩

theorem index_uP :
    (uP.subgroupOf T46).index = 891 := by
  have h := (uP.subgroupOf T46).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe uP_le_T46).toEquiv, card_uP,
    card_T46_eq] at h
  omega

theorem stabilizer_eq_uP :
    MulAction.stabilizer T46 {p : Fin 693 | j3 p = p} = uP.subgroupOf T46 := by
  refine stabilizer_eq_of_le _ _ (fun g hg => ?_) (by rw [index_uP]; exact orbit_fixed_j3)
  rw [MulAction.mem_stabilizer_iff]
  exact smul_fixed_j3 (uP_le_normalizer (Subgroup.mem_subgroupOf.1 hg))

theorem mem_uP_of_smul
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46)
    (h : g • {p : Fin 693 | j3 p = p} = {p | j3 p = p}) : g ∈ uP := by
  have : (⟨g, hg⟩ : T46) ∈ MulAction.stabilizer T46 {p : Fin 693 | j3 p = p} :=
    MulAction.mem_stabilizer_iff.2 h
  rw [stabilizer_eq_uP] at this
  exact Subgroup.mem_subgroupOf.1 this

theorem normalizer_uA
    : T46 ⊓ Subgroup.normalizer (uA : Set (Equiv.Perm (Fin 693))) = uP :=
  le_antisymm (fun _ hg => mem_uP_of_smul hg.1 (smul_fixed_j3 hg.2))
    (le_inf uP_le_T46 uP_le_normalizer)

theorem centralizer_uA
    : T46 ⊓ Subgroup.centralizer (uA : Set (Equiv.Perm (Fin 693))) = uA := by
  refine le_antisymm (fun g hg => ?_) (le_inf uA_le_T46 fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => uA_comm y hy x hx)
  have hgP : g ∈ uP :=
    normalizer_uA ▸ ⟨hg.1, Subgroup.centralizer_le_normalizer _ hg.2⟩
  rw [uP_eq] at hgP
  have hgP' : g ∈ ((uA ⊔ uK : Subgroup (Equiv.Perm (Fin 693))) : Set (Equiv.Perm (Fin 693))) :=
    hgP
  rw [Subgroup.coe_mul_of_right_le_normalizer_left uA uK uK_le_normalizer] at hgP'
  obtain ⟨a, ha, k, hk, rfl⟩ := Set.mem_mul.1 hgP'
  have hk1 : k = 1 := by
    refine eq_one_of_comm_aGens hk fun b hb => ?_
    have hbA := aGens_mem b hb
    have hc := Subgroup.mem_centralizer_iff.1 hg.2 b hbA
    have hab := uA_comm a ha b hbA
    calc k * b = a⁻¹ * ((a * k) * b) := by group
      _ = a⁻¹ * (b * (a * k)) := by rw [hc]
      _ = a⁻¹ * (b * a) * k := by group
      _ = a⁻¹ * (a * b) * k := by rw [hab]
      _ = b * k := by group
  rw [hk1, mul_one]
  exact ha

open CFSG.ComponentClassification.PSL3Four in
theorem beta_facts :
    (∀ i < 42, beta[i]! < 693) ∧ beta.toList.Nodup ∧ beta.size = 42 ∧
      ∀ p ∈ List.zip (kGens.map toTable) [CFSG.PSL3Four.Native.g₁T, CFSG.PSL3Four.Native.g₂T,
        CFSG.PSL3Four.Native.g₃T], ∀ i < 42, ap p.1 beta[i]! = beta[p.2[i]!]! := by
  have h := beta_check
  simp only [betaCheck, Bool.and_eq_true, beq_iff_eq, allIn_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun i hi => h2 i (Nat.zero_le _) hi, h3, h1, fun p hp i hi => h4 p hp i (Nat.zero_le _) hi⟩

theorem betaF_val
    (i : Fin 42) : (betaF i : ℕ) = beta[i.val]! :=
  Nat.mod_eq_of_lt (beta_facts.1 i i.2)

theorem betaF_injective
    : Function.Injective betaF := by
  intro i j hij
  have h := congrArg Fin.val hij
  rw [betaF_val, betaF_val] at h
  have hsz := beta_facts.2.2.1
  rw [getElem!_pos beta i.val (by omega), getElem!_pos beta j.val (by omega),
    ← Array.getElem_toList, ← Array.getElem_toList] at h
  exact Fin.ext ((List.Nodup.getElem_inj_iff beta_facts.2.1).1 h)

open CFSG.ComponentClassification.PSL3Four in
theorem kGens_betaF
    : ∀ m < 3, ∀ i : Fin 42,
    kGens.getD m 1 (betaF i) = betaF ([g₁, g₂, g₃].getD m 1 i) := by
  intro m hm i
  have hT : ∀ m < 3, TabRep ([CFSG.PSL3Four.Native.g₁T, CFSG.PSL3Four.Native.g₂T,
      CFSG.PSL3Four.Native.g₃T].getD m #[]) ([g₁, g₂, g₃].getD m 1) := by
    intro m hm
    interval_cases m
    · exact tabRep_g₁
    · exact tabRep_g₂
    · exact tabRep_g₃
  have hkm : kGens.getD m 1 ∈ kGens := by
    rw [List.getD_eq_getElem _ _ (by simpa [kGens, kWords] using hm)]
    exact List.getElem_mem _
  have hpair : (toTable (kGens.getD m 1), [CFSG.PSL3Four.Native.g₁T, CFSG.PSL3Four.Native.g₂T,
      CFSG.PSL3Four.Native.g₃T].getD m #[]) ∈ List.zip (kGens.map toTable)
      [CFSG.PSL3Four.Native.g₁T, CFSG.PSL3Four.Native.g₂T, CFSG.PSL3Four.Native.g₃T] := by
    interval_cases m <;> simp [kGens, kWords]
  have h := beta_facts.2.2.2 _ hpair i i.2
  simp only at h
  apply Fin.ext
  have hb : (betaF i : ℕ) < 693 := (betaF i).2
  have h1 : ((kGens.getD m 1) (betaF i) : ℕ) = ap (toTable (kGens.getD m 1)) (betaF i) := by
    rw [(rep_toTable hn693 _) _ hb, idx_of_lt _ hb, Equiv.Perm.smul_def]
  rw [h1, betaF_val, betaF_val, h, (hT m hm).apply]

open CFSG.ComponentClassification.PSL3Four in
theorem uK_preserves
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ uK) :
    ∀ x, InOmega (g x) ↔ InOmega x := by
  have hgen : ∀ m < 3, ∀ x, InOmega (kGens.getD m 1 x) ↔ InOmega x := by
    intro m hm x
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨([g₁, g₂, g₃].getD m 1)⁻¹ j, (kGens.getD m 1).injective ?_⟩
      rw [kGens_betaF m hm, perm_apply_inv_self, hj]
    · rintro ⟨i, rfl⟩
      exact ⟨_, (kGens_betaF m hm i).symm⟩
  rw [uK_eq] at hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨m, hm, hmy⟩ := List.getElem_of_mem hy
    have hm3 : m < 3 := by simpa [kGens, kWords] using hm
    have hy' : kGens.getD m 1 = y := by rw [List.getD_eq_getElem _ _ hm, hmy]
    rw [← hy']
    exact hgen m hm3
  | one => exact fun x => Iff.rfl
  | mul y z _ _ hy hz => exact fun x => by rw [Equiv.Perm.mul_apply, hy, hz]
  | inv y _ hy => exact fun x => by rw [← hy (y⁻¹ x), perm_apply_inv_self]

noncomputable def restrictK
    : uK →* Equiv.Perm {x // InOmega x} where
  toFun g := (g : Equiv.Perm (Fin 693)).subtypePerm (uK_preserves g.2)
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def omegaEquiv
    : Fin 42 ≃ {x // InOmega x} :=
  Equiv.ofBijective (fun i => ⟨betaF i, i, rfl⟩)
    ⟨fun _ _ h => betaF_injective (congrArg Subtype.val h), fun ⟨_, i, hi⟩ => ⟨i, Subtype.ext hi⟩⟩

noncomputable def phi42
    : uK →* Equiv.Perm (Fin 42) :=
  (Equiv.permCongrHom omegaEquiv.symm).toMonoidHom.comp restrictK

theorem betaF_phi42
    (g : uK) (i : Fin 42) :
    betaF (phi42 g i) = (g : Equiv.Perm (Fin 693)) (betaF i) := by
  have h : omegaEquiv (phi42 g i) = restrictK g (omegaEquiv i) := by
    simp [phi42, Equiv.permCongrHom, Equiv.permCongr_apply]
  exact congrArg Subtype.val h

open CFSG.ComponentClassification.PSL3Four in
theorem phi42_kGen
    {m : ℕ} (hm : m < 3) :
    phi42 ⟨kGens.getD m 1, kGens_getD_mem hm⟩ = [g₁, g₂, g₃].getD m 1 := by
  ext i
  apply congrArg Fin.val
  apply betaF_injective
  rw [betaF_phi42]
  exact kGens_betaF m hm i

open CFSG.ComponentClassification.PSL3Four in
theorem S_le_range_phi42
    : S ≤ phi42.range := by
  rw [S, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl)
  · exact ⟨_, phi42_kGen (m := 0) (by norm_num)⟩
  · exact ⟨_, phi42_kGen (m := 1) (by norm_num)⟩
  · exact ⟨_, phi42_kGen (m := 2) (by norm_num)⟩

open CFSG.ComponentClassification.PSL3Four in
theorem range_phi42
    : phi42.range = S ∧ Function.Injective phi42 := by
  have hcardR : Nat.card phi42.range * Nat.card phi42.ker = 20160 := by
    rw [← card_uK, Subgroup.card_eq_card_quotient_mul_card_subgroup phi42.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange phi42).toEquiv]
  have hle : Nat.card S ≤ Nat.card phi42.range := Subgroup.card_le_of_le S_le_range_phi42
  rw [card_S] at hle
  have hker : Nat.card phi42.ker = 1 := by
    have hpos : 0 < Nat.card phi42.ker := Nat.card_pos
    by_contra h
    have h2 : Nat.card phi42.range * 2 ≤ Nat.card phi42.range * Nat.card phi42.ker :=
      Nat.mul_le_mul_left _ (by omega)
    rw [hcardR] at h2
    omega
  refine ⟨(Subgroup.eq_of_le_of_card_ge S_le_range_phi42 ?_).symm, ?_⟩
  · rw [card_S]
    rw [hker, mul_one] at hcardR
    omega
  · rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
    exact hker

open CFSG.ComponentClassification.PSL3Four in
noncomputable def uKEquivS :
    uK ≃* S :=
  (MonoidHom.ofInjective range_phi42.2).trans (MulEquiv.subgroupCongr range_phi42.1)

end CFSG.EvenSmallLie.UnitarySix

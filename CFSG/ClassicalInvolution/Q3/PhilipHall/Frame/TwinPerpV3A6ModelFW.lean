module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelSmall
public import Certificates.Certificate517505

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Certificates CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.EvenSmallLie.OmegaEight Certificates.AE6Model Certificates.S7Twin Certificates.S5Rows
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

theorem card_le_length_of_tables {K : Subgroup AE6Om} {C : List Table}
    (hC : ∀ g ∈ K, ∃ T ∈ C, Rep 360 T (g : Equiv.Perm (Fin 360))) : Nat.card K ≤ C.length := by
  classical
  choose f hfC hfR using fun g : K => hC g.1 g.2
  have hinj : Function.Injective
      fun g : K => (⟨f g, List.mem_toFinset.mpr (hfC g)⟩ : C.toFinset) := by
    intro g h hgh
    have hgh' : f g = f h := congrArg Subtype.val hgh
    have hh := hfR h
    rw [← hgh'] at hh
    exact Subtype.ext (Subtype.ext (rep_unique (hfR g) hh))
  calc Nat.card K ≤ Nat.card C.toFinset := Nat.card_le_card_of_injective _ hinj
    _ = C.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ C.length := List.toFinset_card_le C


theorem fw_comm : ∀ X ∈ allTables (wQ ()), ∀ Y ∈ allTables (wQ ()), commT 360 X Y = true := by
  have h : ((allTables (wQ ())).all fun X => (allTables (wQ ())).all fun Y => commT 360 X Y) =
      true := Certificates.certificate517505.1
  intro X hX Y hY
  exact List.all_eq_true.mp (List.all_eq_true.mp h X hX) Y hY

theorem fw_inS : ∀ X ∈ allTables (wQ ()), memT 360 (allTables (sQ ())) X = true := by
  have h : ((allTables (wQ ())).all (memT 360 (allTables (sQ ())))) = true :=
    Certificates.certificate517505.2.1
  exact List.all_eq_true.mp h

theorem fw_norm : ∀ p ∈ twinPairs (), ∀ s ∈ q8Span p.1 p.2, ∀ T ∈ allTables (wQ ()),
    memT 360 (allTables (wQ ())) (conjT 360 (toTable s) (toTable s⁻¹) T) = true := by
  have h : ((twinPairs ()).all fun p => (q8Span p.1 p.2).all fun s =>
      (allTables (wQ ())).all fun T =>
        memT 360 (allTables (wQ ())) (conjT 360 (toTable s) (toTable s⁻¹) T)) = true :=
    Certificates.certificate517505.2.2.1
  intro p hp s hs T hT
  exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h p hp) s hs) T hT

theorem fw_meet : ∀ p ∈ twinPairs (), ∃ x ∈ q8Span p.1 p.2,
    memT 360 (allTables (wQ ())) (toTable x) = true ∧ sqOneT 360 (toTable x) = false ∧
    tblEq 360 (toTable (x * x * x * x)) (idT 360) = true ∧
    ∀ s ∈ q8Span p.1 p.2, memT 360 (allTables (wQ ())) (toTable s) = true →
      memT 360 [idT 360, toTable x, toTable (x * x), toTable (x * x * x)] (toTable s) = true := by
  have h : ((twinPairs ()).all fun p => (q8Span p.1 p.2).any fun x =>
      memT 360 (allTables (wQ ())) (toTable x) && !sqOneT 360 (toTable x) &&
        tblEq 360 (toTable (x * x * x * x)) (idT 360) &&
        (q8Span p.1 p.2).all fun s => !memT 360 (allTables (wQ ())) (toTable s) ||
          memT 360 [idT 360, toTable x, toTable (x * x), toTable (x * x * x)] (toTable s)) =
      true := Certificates.certificate517505.2.2.2.1
  intro p hp
  obtain ⟨x, hx, h1⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    List.all_eq_true] at h1
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h1
  refine ⟨x, hx, h1, h2, h3, fun s hs hsW => ?_⟩
  have := h4 s hs
  rw [hsW, Bool.not_true, Bool.false_or] at this
  exact this

theorem fw_frames : ∀ X0 ∈ frameCands (twinPairs ()) 0, ∀ X1 ∈ frameCands (twinPairs ()) 1,
    ∀ X2 ∈ frameCands (twinPairs ()) 2, ∀ X3 ∈ frameCands (twinPairs ()) 3,
    (((((allTables (sQ ())).filter fun T => commT 360 T X0).filter fun T =>
        commT 360 T X1).filter fun T => commT 360 T X2).filter fun T =>
        commT 360 T X3).length < 64 ∨
      ((((((allTables (sQ ())).filter fun T => commT 360 T X0).filter fun T =>
        commT 360 T X1).filter fun T => commT 360 T X2).filter fun T =>
        commT 360 T X3).length = 64 ∧ ∀ T ∈ allTables (wQ ()),
          commT 360 T X0 = true ∧ commT 360 T X1 = true ∧ commT 360 T X2 = true ∧
            commT 360 T X3 = true) := by
  have h : fwFrames () = true := Certificates.certificate517505.2.2.2.2
  unfold fwFrames at h
  dsimp only at h
  intro X0 h0 X1 h1 X2 h2 X3 h3
  have h' := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp h X0 h0) X1 h1) X2 h2) X3 h3
  rw [Bool.or_eq_true, decide_eq_true_iff, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h'
  rcases h' with h' | ⟨h1', h2'⟩
  · exact Or.inl h'
  · refine Or.inr ⟨h1', fun T hT => ?_⟩
    have := h2' T hT
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem map_W0 : ae6ModelW.map omegaT.subtype = (wQ ()).originalSubgroup := by
  rw [wQ, certificate_originalSubgroup, ae6ModelW, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    w0Gens, wWords, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> rw [coe_ae6Word] <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, by rw [coe_ae6Word]; rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), by rw [coe_ae6Word]; rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), by rw [coe_ae6Word]; rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by rw [coe_ae6Word]; rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr rfl))), by rw [coe_ae6Word]; rfl⟩

theorem mem_W0_iff {y : AE6Om} :
    y ∈ ae6ModelW ↔ (y : Equiv.Perm (Fin 360)) ∈ (wQ ()).originalSubgroup := by
  rw [← map_W0]
  exact (Subgroup.mem_map_iff_mem omegaT.subtype_injective).symm

theorem card_W0 : Nat.card ae6ModelW = 64 := by
  rw [← Subgroup.card_map_of_injective omegaT.subtype_injective, map_W0,
    ← (wQ ()).orderCertificate_eq_card wQ_valid, chains_parts.2.2.2]

theorem memT_W0 {T : Table} {t : Equiv.Perm (Fin 360)} (hT : Rep 360 T t)
    (ht : t ∈ (wQ ()).originalSubgroup) : memT 360 (allTables (wQ ())) T = true :=
  (memT_iff (forall₂_allTables degree_lt (wQ ())) hT).mpr
    (List.mem_reverse.mpr ((mem_enumeration_iff (wQ ()) wQ_valid t).mpr ht))

theorem W0_comm : ∀ x ∈ ae6ModelW, ∀ y ∈ ae6ModelW, x * y = y * x := by
  intro x hx y hy
  obtain ⟨X, hX, hXr⟩ := exists_allTables degree_lt wQ_valid (mem_W0_iff.mp hx)
  obtain ⟨Y, hY, hYr⟩ := exists_allTables degree_lt wQ_valid (mem_W0_iff.mp hy)
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact (commT_iff_commute hXr hYr).mp (fw_comm X hX Y hY)

theorem W0_le_sylow : ae6ModelW ≤ (sQ ()).originalSubgroup.subgroupOf omegaT := by
  intro y hy
  obtain ⟨Y, hY, hYr⟩ := exists_allTables degree_lt wQ_valid (mem_W0_iff.mp hy)
  exact Subgroup.mem_subgroupOf.mpr (mem_of_memT_allTables degree_lt sQ_valid hYr (fw_inS Y hY))

theorem twinPair_mem_omegaT {p : Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)}
    (hp : p ∈ twinPairs ()) :
    Subgroup.closure ({p.1, p.2} : Set (Equiv.Perm (Fin 360))) ≤ omegaT := by
  obtain ⟨c, hc, rfl⟩ := mem_twinPairs.mp hp
  have hk : ∀ x ∈ k0Gens (), x ∈ omegaT := fun x hx => by
    obtain ⟨x', -, rfl⟩ := k0Gens_mem x hx
    exact x'.2
  have hc' := cPerms_mem c hc
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl)
  · exact omegaT.mul_mem (omegaT.mul_mem hc' (hk _ kx_mem)) (omegaT.inv_mem hc')
  · exact omegaT.mul_mem (omegaT.mul_mem hc' (hk _ ky_mem)) (omegaT.inv_mem hc')

theorem twin_le_normalizer_W0 {J : Subgroup AE6Om} (hJ : J ∈ ae6ModelTwins) :
    J ≤ Subgroup.normalizer (ae6ModelW : Set AE6Om) := by
  obtain ⟨g, hg, rfl⟩ := hJ
  obtain ⟨p, hp, hpe⟩ := twin_eq hg
  have hq := q8Rel_twinPair hp
  have hconj : ∀ s : AE6Om, s ∈ conjSub g ae6ModelK → ∀ h ∈ ae6ModelW,
      s * h * s⁻¹ ∈ ae6ModelW := by
    intro s hs h hh
    have hs' := (mem_closure_pair_iff hq).mp ((hpe s).mp hs)
    obtain ⟨T, hT, hTr⟩ := exists_allTables degree_lt wQ_valid (mem_W0_iff.mp hh)
    have h1 := fw_norm p hp _ hs' T hT
    have hrep := rep_conjT (rep_toTable degree_lt (s : Equiv.Perm (Fin 360)))
      (rep_toTable degree_lt (s : Equiv.Perm (Fin 360))⁻¹) hTr
    rw [mem_W0_iff]
    have := mem_of_memT_allTables degree_lt wQ_valid hrep h1
    simpa using this
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj s hs h, fun hh => ?_⟩
  have := hconj s⁻¹ (Subgroup.inv_mem _ hs) _ hh
  rwa [inv_inv, show s⁻¹ * (s * h * s⁻¹) * s = h by group] at this

theorem card_twin_inf_W0 {J : Subgroup AE6Om} (hJ : J ∈ ae6ModelTwins) :
    Nat.card ↥(J ⊓ ae6ModelW) = 4 := by
  obtain ⟨g, hg, rfl⟩ := hJ
  obtain ⟨p, hp, hpe⟩ := twin_eq hg
  have hq := q8Rel_twinPair hp
  have hn := degree_lt
  obtain ⟨x, hx, hxW, hx2, hx4, hxs⟩ := fw_meet p hp
  have hxo : x ∈ omegaT := twinPair_mem_omegaT hp ((mem_closure_pair_iff hq).mpr hx)
  set xA : AE6Om := ⟨x, hxo⟩ with hxA
  have hxJ : xA ∈ conjSub g ae6ModelK := (hpe xA).mpr ((mem_closure_pair_iff hq).mpr hx)
  have hxW0 : xA ∈ ae6ModelW :=
    mem_W0_iff.mpr (mem_of_memT_allTables hn wQ_valid (rep_toTable hn x) hxW)
  have heq : conjSub g ae6ModelK ⊓ ae6ModelW = Subgroup.zpowers xA := by
    apply le_antisymm
    · intro t ht
      obtain ⟨htJ, htW⟩ := Subgroup.mem_inf.mp ht
      have hts := (mem_closure_pair_iff hq).mp ((hpe t).mp htJ)
      have h1 := hxs _ hts (memT_W0 (rep_toTable hn _) (mem_W0_iff.mp htW))
      have hF : List.Forall₂ (Rep 360) [idT 360, toTable x, toTable (x * x), toTable (x * x * x)]
          [1, x, x * x, x * x * x] :=
        .cons (Rep.idT hn) (.cons (rep_toTable hn _) (.cons (rep_toTable hn _)
          (.cons (rep_toTable hn _) .nil)))
      rw [memT_iff hF (rep_toTable hn _)] at h1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      have ht' : ∀ k : ℕ, (t : Equiv.Perm (Fin 360)) = x ^ k → t ∈ Subgroup.zpowers xA :=
        fun k hk => ⟨(k : ℤ), Subtype.ext (by simp [hxA, hk])⟩
      rcases h1 with h1 | h1 | h1 | h1
      · exact ht' 0 (by simpa using h1)
      · exact ht' 1 (by simpa using h1)
      · exact ht' 2 (by rw [h1, sq])
      · exact ht' 3 (by rw [h1, pow_succ, sq])
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨hxJ, hxW0⟩
  rw [heq, Nat.card_zpowers, ← Subgroup.orderOf_coe]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ¬ x ^ 2 ^ 1 = 1 := by
    intro h
    rw [pow_one, sq] at h
    rw [(sqOneT_iff hn (rep_toTable hn x)).mpr h] at hx2
    exact Bool.noConfusion hx2
  have h4 : x ^ 2 ^ (1 + 1) = 1 := by
    rw [tblEq_iff_eq (rep_toTable hn _) (Rep.idT hn)] at hx4
    calc x ^ 2 ^ (1 + 1) = x * x * x * x := by norm_num [pow_succ]
      _ = 1 := hx4
  exact orderOf_eq_prime_pow h2 h4

theorem admissible_W0 : AE6Admissible ae6ModelW :=
  ⟨W0_comm, card_W0, fun _ hJ => ⟨twin_le_normalizer_W0 hJ, card_twin_inf_W0 hJ⟩⟩

theorem exists_conj_into_sylow {P : Subgroup AE6Om} (hP : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) :
    ∃ a ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om),
      ∀ w ∈ P, a⁻¹ * w * a ∈ (sQ ()).originalSubgroup.subgroupOf omegaT := by
  have hodd : ¬ 2 ∣ (((sQ ()).originalSubgroup.subgroupOf omegaT).subgroupOf
      (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om))).index := by
    intro h
    apply index_sylow
    rw [← Subgroup.relIndex_mul_index sylow_le_CZ]
    exact Dvd.dvd.mul_right h _
  have hP' : IsPGroup 2 (P.subgroupOf (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om))) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  obtain ⟨a, ha⟩ := exists_conj_le_of_odd_index hodd hP'
  refine ⟨a, a.2, fun w hw => ?_⟩
  exact Subgroup.mem_subgroupOf.mp (ha ⟨w, hPC hw⟩ (Subgroup.mem_subgroupOf.mpr hw))

theorem twinPair_mem_twins {p : Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)}
    (hp : p ∈ twinPairs ()) :
    (Subgroup.closure ({p.1, p.2} : Set (Equiv.Perm (Fin 360)))).subgroupOf omegaT ∈
      ae6ModelTwins := by
  obtain ⟨c, hc, rfl⟩ := mem_twinPairs.mp hp
  refine ⟨⟨c, cPerms_mem c hc⟩, mem_CZ (cPerms_mem c hc) (cPerms_comm c hc), ?_⟩
  ext x
  rw [mem_conjSub_K0_iff, Subgroup.mem_subgroupOf]

theorem exists_frame_elt {p : Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)}
    (hp : p ∈ twinPairs ()) {W : Subgroup AE6Om}
    (hW : Nat.card ↥((Subgroup.closure ({p.1, p.2} : Set (Equiv.Perm (Fin 360)))).subgroupOf
      omegaT ⊓ W) = 4) :
    ∃ t ∈ W, (t : Equiv.Perm (Fin 360)) ∈ q8Span p.1 p.2 ∧
      (t : Equiv.Perm (Fin 360)) * t ≠ 1 := by
  have hq := q8Rel_twinPair hp
  have hu := isUniqueInvolution_closure_pair hq
  by_contra hno
  push Not at hno
  set M := (Subgroup.closure ({p.1, p.2} : Set (Equiv.Perm (Fin 360)))).subgroupOf omegaT ⊓ W
  set zA : AE6Om := ⟨p.1 * p.1, twinPair_mem_omegaT hp hu.mem⟩
  have hsub : (M : Set AE6Om) ⊆ {1, zA} := by
    intro t ht
    obtain ⟨htT, htW⟩ := Subgroup.mem_inf.mp ht
    have htT' := Subgroup.mem_subgroupOf.mp htT
    have h1 := hno t htW ((mem_closure_pair_iff hq).mp htT')
    rcases hu.unique _ htT' h1 with h2 | h2
    · left
      exact Subtype.ext h2
    · right
      exact Subtype.ext h2
  have hle : Nat.card ↥M ≤ 2 := by
    rw [show Nat.card ↥M = Nat.card ↥(M : Set AE6Om) from rfl, Nat.card_coe_set_eq]
    calc (M : Set AE6Om).ncard ≤ ({1, zA} : Set AE6Om).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({zA} : Set AE6Om).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  omega

theorem admissible_conj (W₁ : Subgroup AE6Om) (hW : AE6Admissible W₁) :
    ∃ c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om), conjSub c ae6ModelW = W₁ := by
  obtain ⟨hcomm, hcard, htw⟩ := hW
  have hn := degree_lt
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ae6ModelK ∈ ae6ModelTwins := ⟨1, Subgroup.one_mem _, conjSub_one _⟩
  have hz : ae6ModelZ ∈ W₁ := by
    have h4 := (htw _ hK).2
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(ae6ModelK ⊓ W₁)) 2
      (by rw [h4]; norm_num)
    have ht' : orderOf (t : AE6Om) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    have htK : (t : AE6Om) ∈ ae6ModelK := (Subgroup.mem_inf.mp t.2).1
    have htW : (t : AE6Om) ∈ W₁ := (Subgroup.mem_inf.mp t.2).2
    have htt : (t : AE6Om) * t = 1 := by
      rw [← sq, ← ht']
      exact pow_orderOf_eq_one _
    have ht1 : (t : AE6Om) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at ht'
      exact absurd ht' (by norm_num)
    rcases smallQ8_K0.2.1.unique _ htK htt with h1 | h1
    · exact absurd h1 ht1
    · rwa [← h1]
  have hW1C : W₁ ≤ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) := fun w hw => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm w hw _ hz
  have hP : IsPGroup 2 W₁ := IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)
  obtain ⟨a, haC, ha⟩ := exists_conj_into_sylow hP hW1C
  set W₂ := conjSub a⁻¹ W₁ with hW₂
  have hmemW₂ : ∀ {y : AE6Om}, y ∈ W₂ ↔ a * y * a⁻¹ ∈ W₁ := fun {y} => by
    rw [hW₂, mem_conjSub_iff, inv_inv]
  have hW2S : ∀ y ∈ W₂, (y : Equiv.Perm (Fin 360)) ∈ (sQ ()).originalSubgroup := by
    intro y hy
    have := ha _ (hmemW₂.mp hy)
    rw [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hW2comm : ∀ x ∈ W₂, ∀ y ∈ W₂, x * y = y * x := by
    intro x hx y hy
    have h1 := hcomm _ (hmemW₂.mp hx) _ (hmemW₂.mp hy)
    calc x * y = a⁻¹ * ((a * x * a⁻¹) * (a * y * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * y * a⁻¹) * (a * x * a⁻¹)) * a := by rw [h1]
      _ = y * x := by group
  have hcc : ∀ (g : AE6Om) (H : Subgroup AE6Om), Nat.card (conjSub g H) = Nat.card H :=
    fun g _ => Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hW2card : Nat.card W₂ = 64 := by rw [hW₂, hcc, hcard]
  have hinf : ∀ (g : AE6Om) (A B : Subgroup AE6Om),
      conjSub g (A ⊓ B) = conjSub g A ⊓ conjSub g B := fun g A B => by
    unfold conjSub
    exact Subgroup.map_inf_eq A B _ (MulAut.conj g).injective
  have hW2meet : ∀ p ∈ twinPairs (), Nat.card ↥((Subgroup.closure
      ({p.1, p.2} : Set (Equiv.Perm (Fin 360)))).subgroupOf omegaT ⊓ W₂) = 4 := by
    intro p hp
    have hT := twinPair_mem_twins hp
    have haT : conjSub a ((Subgroup.closure
        ({p.1, p.2} : Set (Equiv.Perm (Fin 360)))).subgroupOf omegaT) ∈ ae6ModelTwins := by
      obtain ⟨g, hg, hgT⟩ := hT
      exact ⟨a * g, Subgroup.mul_mem _ haC hg, by rw [conjSub_mul, hgT]⟩
    rw [hW₂, ← conjSub_inv_conjSub a ((Subgroup.closure
      ({p.1, p.2} : Set (Equiv.Perm (Fin 360)))).subgroupOf omegaT), ← hinf, hcc,
      (htw _ haT).2]
  have hlen : (twinPairs ()).length = 4 := sm_k0.2.2
  have hpk : ∀ k < 4, (twinPairs ()).getD k (1, 1) ∈ twinPairs () := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hk)]
    exact List.getElem_mem _
  have hfr : ∀ k < 4, ∃ t ∈ W₂,
      toTable (t : Equiv.Perm (Fin 360)) ∈ frameCands (twinPairs ()) k := by
    intro k hk
    obtain ⟨t, htW, hts, htt⟩ := exists_frame_elt (hpk k hk) (hW2meet _ (hpk k hk))
    refine ⟨t, htW, ?_⟩
    have hsq : sqOneT 360 (toTable (t : Equiv.Perm (Fin 360))) = false := by
      cases h : sqOneT 360 (toTable (t : Equiv.Perm (Fin 360))) with
      | false => rfl
      | true => exact absurd ((sqOneT_iff hn (rep_toTable hn _)).mp h) htt
    exact List.mem_filter.mpr ⟨List.mem_map_of_mem hts, by simp [hsq]⟩
  obtain ⟨t0, ht0, hT0⟩ := hfr 0 (by norm_num)
  obtain ⟨t1, ht1, hT1⟩ := hfr 1 (by norm_num)
  obtain ⟨t2, ht2, hT2⟩ := hfr 2 (by norm_num)
  obtain ⟨t3, ht3, hT3⟩ := hfr 3 (by norm_num)
  set Cx := (sQ ()).originalSubgroup.subgroupOf omegaT ⊓
    Subgroup.centralizer ({t0, t1, t2, t3} : Set AE6Om) with hCx
  set C := ((((allTables (sQ ())).filter fun T =>
      commT 360 T (toTable (t0 : Equiv.Perm (Fin 360)))).filter fun T =>
      commT 360 T (toTable (t1 : Equiv.Perm (Fin 360)))).filter fun T =>
      commT 360 T (toTable (t2 : Equiv.Perm (Fin 360)))).filter fun T =>
      commT 360 T (toTable (t3 : Equiv.Perm (Fin 360))) with hC
  have hcC : ∀ g ∈ Cx, ∃ T ∈ C, Rep 360 T (g : Equiv.Perm (Fin 360)) := by
    intro g hg
    obtain ⟨hgS, hgC⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨T, hT, hTr⟩ := exists_allTables hn sQ_valid (Subgroup.mem_subgroupOf.mp hgS)
    rw [Subgroup.mem_centralizer_iff] at hgC
    have hc : ∀ t ∈ ({t0, t1, t2, t3} : Set AE6Om),
        commT 360 T (toTable (t : Equiv.Perm (Fin 360))) = true := fun t ht => by
      rw [commT_iff_commute hTr (rep_toTable hn _)]
      have := congrArg Subtype.val (hgC t ht)
      simp only [Subgroup.coe_mul] at this
      exact this.symm
    refine ⟨T, ?_, hTr⟩
    simp only [hC, List.mem_filter]
    exact ⟨⟨⟨⟨hT, hc t0 (by simp)⟩, hc t1 (by simp)⟩, hc t2 (by simp)⟩, hc t3 (by simp)⟩
  have hCcard : Nat.card Cx ≤ C.length := card_le_length_of_tables hcC
  have hW2Cx : W₂ ≤ Cx := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr (hW2S y hy), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro t (rfl | rfl | rfl | rfl)
    · exact hW2comm _ ht0 y hy
    · exact hW2comm _ ht1 y hy
    · exact hW2comm _ ht2 y hy
    · exact hW2comm _ ht3 y hy
  have hW2le := Subgroup.card_le_of_le hW2Cx
  rcases fw_frames _ hT0 _ hT1 _ hT2 _ hT3 with hlt | ⟨heq64, hWT⟩
  · exfalso
    rw [← hC] at hlt
    have h64 : 64 ≤ C.length := hW2card ▸ hW2le.trans hCcard
    omega
  · rw [← hC] at heq64
    have hW0Cx : ae6ModelW ≤ Cx := by
      intro y hy
      refine Subgroup.mem_inf.mpr ⟨W0_le_sylow hy, ?_⟩
      obtain ⟨Y, hY, hYr⟩ := exists_allTables hn wQ_valid (mem_W0_iff.mp hy)
      obtain ⟨c0, c1, c2, c3⟩ := hWT Y hY
      have hc : ∀ t : AE6Om, commT 360 Y (toTable (t : Equiv.Perm (Fin 360))) = true →
          t * y = y * t := fun t h => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact ((commT_iff_commute hYr (rep_toTable hn _)).mp h).symm
      rw [Subgroup.mem_centralizer_iff]
      rintro t (rfl | rfl | rfl | rfl)
      · exact hc _ c0
      · exact hc _ c1
      · exact hc _ c2
      · exact hc _ c3
    have hW2eq : W₂ = Cx :=
      Subgroup.eq_of_le_of_card_ge hW2Cx ((hCcard.trans heq64.le).trans hW2card.symm.le)
    have hW0eq : ae6ModelW = Cx :=
      Subgroup.eq_of_le_of_card_ge hW0Cx ((hCcard.trans heq64.le).trans card_W0.symm.le)
    refine ⟨a, haC, ?_⟩
    rw [hW0eq, ← hW2eq, hW₂, conjSub_conjSub_inv]

theorem ae6ModelFW_proved : AE6ModelFW :=
  ⟨admissible_W0, admissible_conj⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

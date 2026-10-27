module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Lin2Act
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatural
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement MatrixGroups LinearAlgebra.Projectivization

namespace C56

variable {G : Type} [Group G]

omit [Group G] in
theorem sl2_eq_one_of_forall_smul_eq {F : Type*} [Field F] {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : ∀ w : Fin 2 → F, g • w = w) : g = 1 := by
  apply Subtype.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at this
  simp [Matrix.mulVec_single] at this
  fin_cases i <;> fin_cases j <;> simp_all

variable [Finite G]

theorem lin2_exists_point {L T : Subgroup G} {n : ℕ} (hn : 1 ≤ n) (hT : IsSylowTwoOf T L)
    {F : Type} [Field F] [Fintype F] (hq : Nat.card F = 2 ^ n) [CharP F 2]
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) :
    ∃ p : ℙ F (Fin 2 → F), (T.subgroupOf L).map α = rootGrp p ∧
      ∀ l : L, α l ∈ rootGrp p ↔ (l : G) ∈ T := by
  classical
  have hQT : blockQ L ≤ T :=
    hT.le_of_normalizes (C1.blockQ_le L) (C1.le_normalizer_blockQ L) (C1.blockQ_isPGroup L)
  have hT1 : ∀ l : L, l ∈ α.ker ↔ (l : G) ∈ blockQ L := fun l => by
    rw [hαk]; exact (mem_blockQ_iff l).symm
  have hker_le : α.ker ≤ T.subgroupOf L := fun l hl => hQT ((hT1 l).mp hl)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := RankOneRecog.isSylowTwoOf_iff_exists.mp hT
  have hPT : (P : Subgroup L) = T.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hP, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT.le]
  let P' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) := P.mapSurjective hαs
  have hP'eq : (P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      (T.subgroupOf L).map α := by
    show (P : Subgroup L).map α = _
    rw [hPT]
  have hfac : (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)).factorization 2 = n := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq]
    have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
    have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have hodd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by omega
    rw [Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hP'card : Nat.card (P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      Nat.card F := by
    rw [P'.card_eq_multiplicity, hfac, hq]
  obtain ⟨p, hp⟩ := exists_point_eq_rootGrp (p := 2) (f := n) Nat.prime_two hq hP'card
  have hTp : (T.subgroupOf L).map α = rootGrp p := hP'eq ▸ hp
  have hT2 : ∀ l : L, α l ∈ rootGrp p ↔ (l : G) ∈ T := by
    intro l
    rw [← hTp]
    constructor
    · rintro ⟨l', hl', hll'⟩
      have h1 : l'⁻¹ * l ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hll', inv_mul_cancel]
      have h2 : l'⁻¹ * l ∈ T.subgroupOf L := hker_le h1
      have h3 := mul_mem hl' h2
      rw [mul_inv_cancel_left] at h3
      exact h3
    · intro hl
      exact ⟨l, hl, rfl⟩
  exact ⟨p, hTp, hT2⟩

theorem lin2_module_facts {L T : Subgroup G} (hL : IsShort2 L) {n : ℕ} (hn : 1 ≤ n)
    (hlin : IsLin2Type L n) (hT : IsSylowTwoOf T L) :
    L ⊓ centralizer (blockU L : Set G) = blockQ L ∧
    (blockQ L).relIndex T = 2 ^ n ∧
    (blockU L ⊓ centralizer (T : Set G)).relIndex (blockU L) = 2 ^ n ∧
    ⁅blockU L, T⁆ = blockU L ⊓ centralizer (T : Set G) ∧
    (∀ t ∈ T, t ∉ blockQ L → ∀ u ∈ blockU L, (u * t = t * u ↔ u ∈ centralizer (T : Set G))) ∧
    ∃ k ∈ L, L ≤ T ⊔ conjSubgroup T k := by
  classical
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hlin
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hq
  have hUab : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := (C1.elemAb2_blockU hL).1
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hL).trans (C1.blockQ_le L)
  have hLN : L ≤ normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
  have hQT : blockQ L ≤ T :=
    hT.le_of_normalizes (C1.blockQ_le L) (C1.le_normalizer_blockQ L) (C1.blockQ_isPGroup L)
  let conjL : ↥L →* MulAut ↥(blockU L) :=
    (blockU L).normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  have hconjL : ∀ (l : L) (u : blockU L), ((conjL l u : blockU L) : G) = l * u * l⁻¹ :=
    fun l u => rfl
  have hkerle : α.ker ≤ conjL.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rw [hconjL, MulAut.one_apply]
    have hlQ : (l : G) ∈ blockQ L := (mem_blockQ_iff l).mpr (hαk ▸ hl)
    have := C1.blockU_comm hL u u.2 l hlQ
    rw [Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
    exact this.symm
  let act : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut ↥(blockU L) :=
    MonoidHom.liftOfRightInverse α (Function.surjInv hαs) (Function.rightInverse_surjInv hαs)
      ⟨conjL, hkerle⟩
  have hact : ∀ l : L, act (α l) = conjL l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hαs)
      (Function.rightInverse_surjInv hαs) ⟨conjL, hkerle⟩ l
  have hactc : ∀ (l : L) (u : blockU L), ((act (α l) u : blockU L) : G) = l * u * l⁻¹ := by
    intro l u
    rw [hact, hconjL]
  let hCG : CommGroup ↥(blockU L) :=
    { (inferInstance : Group ↥(blockU L)) with
      mul_comm := fun a b => Subtype.ext (hUab _ a.2 _ b.2) }
  have hIs : IsNatPlane act β := by
    refine ⟨?_, hβs, ?_, ?_⟩
    · intro e
      apply Subtype.ext
      have := C1.blockU_sq hL e e.2
      simpa [pow_two] using this
    · intro g e
      obtain ⟨l, rfl⟩ := hαs g
      rw [hact]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
      exact hβe l e (conjL l e) (hconjL l e)
    · intro g e he
      obtain ⟨l, rfl⟩ := hαs g
      rw [hact]
      have heZ : (e : G) ∈ blockZ L := by
        have : e ∈ (blockZ L).subgroupOf (blockU L) := hβk ▸ he
        exact this
      apply Subtype.ext
      rw [hconjL]
      have := Subgroup.mem_centralizer_iff.mp heZ.2 (l : G) l.2
      rw [Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
      exact this
  have hEL : commSub act Set.univ ⊤ = ⊤ := by
    rw [eq_top_iff]
    intro e _
    have hUK : blockU L ≤ (commSub act Set.univ ⊤).map (blockU L).subtype := by
      refine (C1.commutator_blockU hL).symm.le.trans ?_
      rw [Subgroup.commutator_le]
      intro u hu l hl
      have hgen : act (α ⟨l, hl⟩) ⟨u, hu⟩ * (⟨u, hu⟩ : blockU L)⁻¹ ∈ commSub act Set.univ ⊤ :=
        Subgroup.subset_closure ⟨α ⟨l, hl⟩, Set.mem_univ _, ⟨u, hu⟩, Subgroup.mem_top _, rfl⟩
      refine ⟨(act (α ⟨l, hl⟩) ⟨u, hu⟩ * (⟨u, hu⟩ : blockU L)⁻¹)⁻¹, inv_mem hgen, ?_⟩
      show (((act (α ⟨l, hl⟩) ⟨u, hu⟩ * (⟨u, hu⟩ : blockU L)⁻¹)⁻¹ : blockU L) : G) = ⁅u, l⁆
      rw [commutatorElement_def]
      simp [hactc]
      group
    obtain ⟨k, hk, hke⟩ := hUK e.2
    have : k = e := Subtype.ext hke
    rwa [this] at hk
  obtain ⟨-, hpall⟩ := saturated_natural_plane_root_fixed_space (k := F) (E := ↥(blockU L)) hn hq
    hIs hEL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, hTp, hT2⟩ := lin2_exists_point hn hT hq α hαs hαk
  have hT1 : ∀ l : L, l ∈ α.ker ↔ (l : G) ∈ blockQ L := fun l => by
    rw [hαk]; exact (mem_blockQ_iff l).symm
  have hker_le : α.ker ≤ T.subgroupOf L := fun l hl => hQT ((hT1 l).mp hl)
  have hR1 : L ⊓ centralizer (blockU L : Set G) = blockQ L := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ⟨C1.blockQ_le L hg, ?_⟩)
    · obtain ⟨hgL, hgc⟩ := hg
      have h1 : α ⟨g, hgL⟩ = 1 := by
        apply sl2_eq_one_of_forall_smul_eq
        intro w
        obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
        have hcomm : (u : G) * g = g * u := Subgroup.mem_centralizer_iff.mp hgc u u.2
        have hconj : (u : G) = g * u * g⁻¹ := by
          rw [eq_comm, mul_inv_eq_iff_eq_mul]; exact hcomm.symm
        have := hβe ⟨g, hgL⟩ u u (by simpa using hconj)
        rw [hu, toAdd_ofAdd] at this
        rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
        exact this.symm
      exact (hT1 ⟨g, hgL⟩).mp (MonoidHom.mem_ker.mpr h1)
    · exact Subgroup.mem_centralizer_iff.mpr fun u hu => C1.blockU_comm hL u hu g hg
  have hR2 : (blockQ L).relIndex T = 2 ^ n := by
    have hcT : Nat.card T = Nat.card (blockQ L) * (blockQ L).relIndex T :=
      C5.card_eq_card_mul_relIndex hQT
    have hcTl : Nat.card (T.subgroupOf L) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.le).toEquiv
    have h1 := Subgroup.card_ker_mul_card_range (α.domRestrict (T.subgroupOf L))
    rw [MonoidHom.domRestrict_range, hTp, MonoidHom.ker_domRestrict, card_rootGrp, hq] at h1
    have h2 : Nat.card (α.ker.subgroupOf (T.subgroupOf L)) = Nat.card (blockQ L) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv, blockQ_eq_map,
        Subgroup.card_map_of_injective L.subtype_injective, hαk]
    rw [h2, hcTl, hcT] at h1
    have hpos : 0 < Nat.card (blockQ L) := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  obtain ⟨t₁, ht₁, ht₁1⟩ := exists_ne_one_mem_rootGrp (k := F) p
  obtain ⟨hfix, hcomm, -, hts, -, -⟩ := hpall p
  have hFixU : (blockU L ⊓ centralizer (T : Set G)).subgroupOf (blockU L) =
      fixedSub act (rootGrp p : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    ext u
    rw [Subgroup.mem_subgroupOf, mem_fixedSub]
    constructor
    · rintro ⟨-, hu⟩ a ha
      obtain ⟨l, rfl⟩ := hαs a
      have hlT : (l : G) ∈ T := (hT2 l).mp ha
      apply Subtype.ext
      rw [hactc]
      have := Subgroup.mem_centralizer_iff.mp hu (l : G) hlT
      rw [Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
      exact this
    · intro h
      refine ⟨u.2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      have hl : α ⟨t, hT.le ht⟩ ∈ rootGrp p := (hT2 ⟨t, hT.le ht⟩).mpr ht
      have := congrArg (fun x : blockU L => (x : G)) (h _ hl)
      simp only [hactc] at this
      rw [Subgroup.coe_inv] at this
      exact (mul_inv_eq_iff_eq_mul.mp this)
  have hR3 : (blockU L ⊓ centralizer (T : Set G)).relIndex (blockU L) = 2 ^ n := by
    show ((blockU L ⊓ centralizer (T : Set G)).subgroupOf (blockU L)).index = 2 ^ n
    rw [hFixU, ← hq]
    exact (hts t₁ ht₁ ht₁1).2.1
  have hdisp : ∀ (t : G) (ht : t ∈ T) (u : blockU L),
      ((u * (act (α ⟨t, hT.le ht⟩) u)⁻¹ : blockU L) : G) = ⁅(u : G), t⁆ := by
    intro t ht u
    show (u : G) * ((act (α ⟨t, hT.le ht⟩) u : blockU L) : G)⁻¹ = _
    rw [hactc, commutatorElement_def]
    simp [mul_assoc]
  have hR4 : ⁅blockU L, T⁆ = blockU L ⊓ centralizer (T : Set G) := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu t ht
      have hmemU : ⁅u, t⁆ ∈ blockU L := by
        have h1 : t * u⁻¹ * t⁻¹ ∈ blockU L :=
          (Subgroup.mem_normalizer_iff.mp (hLN (hT.le ht)) _).mp (inv_mem hu)
        have := mul_mem hu h1
        rw [commutatorElement_def]
        simpa [mul_assoc] using this
      refine ⟨hmemU, ?_⟩
      have hmem : (⟨⁅u, t⁆, hmemU⟩ : blockU L) ∈ fixedSub act (rootGrp p : Set _) := by
        rw [hfix]
        show β ⟨⁅u, t⁆, hmemU⟩ ∈ lineMult p
        have h1 : (⟨⁅u, t⁆, hmemU⟩ : blockU L) = ⟨u, hu⟩ * (act (α ⟨t, hT.le ht⟩) ⟨u, hu⟩)⁻¹ :=
          Subtype.ext (hdisp t ht ⟨u, hu⟩).symm
        rw [h1, map_mul, map_inv, mem_lineMult, toAdd_mul, toAdd_inv, hIs.toAdd_smul_eq]
        have := (mem_rootGrp.mp ((hT2 ⟨t, hT.le ht⟩).mpr ht))
          (Multiplicative.toAdd (β ⟨u, hu⟩))
        have h2 := Submodule.neg_mem _ this
        simpa [sub_eq_add_neg, add_comm] using h2
      rw [← hFixU] at hmem
      exact (Subgroup.mem_subgroupOf.mp hmem).2
    · intro w hw
      have hwU : w ∈ blockU L := hw.1
      have hmem : (⟨w, hwU⟩ : blockU L) ∈ commSub act (rootGrp p : Set _) ⊤ := by
        rw [← hcomm, ← hfix, ← hFixU]
        exact Subgroup.mem_subgroupOf.mpr hw
      have hle : commSub act (rootGrp p : Set _) ⊤ ≤ (⁅blockU L, T⁆).comap (blockU L).subtype := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨a, ha, e, -, rfl⟩
        obtain ⟨l, rfl⟩ := hαs a
        have hlT : (l : G) ∈ T := (hT2 l).mp ha
        show (((act (α l) e * e⁻¹ : blockU L)) : G) ∈ ⁅blockU L, T⁆
        have : (((act (α l) e * e⁻¹ : blockU L)) : G) = ⁅(l : G), (e : G)⁆ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hactc, commutatorElement_def]
          simp
        rw [this, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hlT e.2
      exact hle hmem
  have hR5 : ∀ t ∈ T, t ∉ blockQ L → ∀ u ∈ blockU L,
      (u * t = t * u ↔ u ∈ centralizer (T : Set G)) := by
    intro t ht htQ u hu
    have htL : t ∈ L := hT.le ht
    have hα1 : α ⟨t, htL⟩ ≠ 1 := fun h => htQ ((hT1 ⟨t, htL⟩).mp (MonoidHom.mem_ker.mpr h))
    have hαp : α ⟨t, htL⟩ ∈ rootGrp p := (hT2 _).mpr ht
    have hsingle := (hts _ hαp hα1).1
    constructor
    · intro hut
      have h1 : (⟨u, hu⟩ : blockU L) ∈ fixedSub act ({α ⟨t, htL⟩} : Set _) := by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        apply Subtype.ext
        rw [hactc, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
        exact hut.symm
      rw [hsingle, ← hFixU] at h1
      exact (Subgroup.mem_subgroupOf.mp h1).2
    · intro huT
      have := Subgroup.mem_centralizer_iff.mp huT t ht
      exact this.symm
  have hR6 : ∃ k ∈ L, L ≤ T ⊔ conjSubgroup T k := by
    obtain ⟨m, hm⟩ := exists_ne_point (k := F) p
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) F) p m
    obtain ⟨k, hk⟩ := hαs g⁻¹
    refine ⟨k, k.2, ?_⟩
    set K : Subgroup L := (T ⊔ conjSubgroup T k).subgroupOf L with hK
    have hTK : T.subgroupOf L ≤ K := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
    have h1 : rootGrp p ≤ K.map α := by
      intro g' hg'
      rw [← hTp] at hg'
      obtain ⟨x, hx, rfl⟩ := hg'
      exact ⟨x, hTK hx, rfl⟩
    have h2 : rootGrp m ≤ K.map α := by
      intro g' hg'
      rw [← hg, mem_rootGrp_smul_iff, ← hTp] at hg'
      obtain ⟨t₀, ht₀, ht₀e⟩ := hg'
      refine ⟨k⁻¹ * t₀ * k, ?_, ?_⟩
      · refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ?_)
        rw [mem_conjSubgroup_iff]
        have : (k : G) * ((k⁻¹ * t₀ * k : L) : G) * (k : G)⁻¹ = (t₀ : G) := by
          simp [mul_assoc]
        rw [this]
        exact Subgroup.mem_subgroupOf.mp ht₀
      · rw [map_mul, map_mul, map_inv, hk, ht₀e]
        group
    have h3 : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ K.map α := by
      rw [← rootGrp_sup_rootGrp hm.symm]
      exact sup_le h1 h2
    intro l hl
    obtain ⟨x, hxK, hxl⟩ := h3 (Subgroup.mem_top (α ⟨l, hl⟩))
    have hker : x⁻¹ * ⟨l, hl⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxl, inv_mul_cancel]
    have h4 : x⁻¹ * ⟨l, hl⟩ ∈ K := hTK (hker_le hker)
    have h5 := mul_mem hxK h4
    rw [mul_inv_cancel_left] at h5
    exact Subgroup.mem_subgroupOf.mp h5
  exact ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩

end C56

end CFSG.QuasithinUnique

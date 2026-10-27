module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroLift
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def wSup (Q : Type) [Group Q] : Subgroup Q :=
  ⨆ T ∈ {T : Subgroup Q | IsSubnormal T ⊤ ∧ (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}, T

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barHom (M X : Subgroup G) (hX : X ≤ M) : ↥X →* ↥(barM M X) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (inclusion hX)).codRestrict (barM M X)
    (fun x => ⟨inclusion hX x, x.2, rfl⟩)

@[simp] theorem coe_barHom (M X : Subgroup G) (hX : X ≤ M) (x : ↥X) :
    ((barHom M X hX x : ↥(barM M X)) : ↥M ⧸ CFSG.pCore 2 ↥M) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (inclusion hX x) := rfl

theorem barHom_surjective (M X : Subgroup G) (hX : X ≤ M) :
    Function.Surjective (barHom M X hX) := by
  rintro ⟨y, m, hm, rfl⟩
  refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
  rw [coe_barHom]
  rfl

theorem mem_ker_barHom {M X : Subgroup G} {hX : X ≤ M} {x : ↥X} :
    x ∈ (barHom M X hX).ker ↔ (x : G) ∈ pCoreOf 2 M := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff, coe_barHom, OneMemClass.coe_one,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = inclusion hX x := Subtype.ext hyx
    rwa [← this]

theorem isPGroup_ker_barHom (M X : Subgroup G) (hX : X ≤ M) :
    IsPGroup 2 (barHom M X hX).ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (barHom M X hX).ker = (CFSG.pCore 2 ↥M).comap (inclusion hX) := by
    ext x
    rw [mem_ker_barHom, mem_comap]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = inclusion hX x := Subtype.ext hyx
      rwa [← this]
    · intro h
      exact ⟨_, h, rfl⟩
  rw [h]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).comap_of_injective _ (inclusion_injective hX)

@[expose] noncomputable def hatHom (M X : Subgroup G) (hX : X ≤ M) :
    ↥X →* ↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X) :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M X))).comp (barHom M X hX)

theorem hatHom_surjective (M X : Subgroup G) (hX : X ≤ M) :
    Function.Surjective (hatHom M X hX) :=
  (QuotientGroup.mk'_surjective _).comp (barHom_surjective M X hX)

theorem isPGroup_ker_hatHom (M X : Subgroup G) (hX : X ≤ M) :
    IsPGroup 2 (hatHom M X hX).ker := by
  rw [hatHom, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact IsPGroup.comap_of_ker_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := ↥(barM M X))) _
    (isPGroup_ker_barHom M X hX)

theorem pCore_hat_eq_bot (M X : Subgroup G) :
    CFSG.pCore 2 (↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X)) = ⊥ :=
  pCore_quotient_pCore_eq_bot' 2

theorem pCoreOf_eq_map_ker (M X : Subgroup G) (hX : X ≤ M) :
    pCoreOf 2 X = (hatHom M X hX).ker.map X.subtype := by
  unfold pCoreOf
  rw [CZeroLift.pCore_eq_ker _ (hatHom_surjective M X hX) (isPGroup_ker_hatHom M X hX)
    (pCore_hat_eq_bot M X)]

theorem wSup_le_map_jZero (M H L : Subgroup G) (hX : H ⊓ L ≤ M) :
    wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L))) ≤
      ((jZero H L).subgroupOf (H ⊓ L)).map (hatHom M (H ⊓ L) hX) := by
  refine iSup₂_le fun T hT => ?_
  have hlift : ∃ I ∈ cZero (H ⊓ L), (I.subgroupOf (H ⊓ L)).map (hatHom M (H ⊓ L) hX) = T := by
    rcases hT.2 with hc | hb
    · exact CZeroLift.exists_cZero_of_component _ (hatHom_surjective _ _ hX)
        (isPGroup_ker_hatHom _ _ hX) (pCore_hat_eq_bot _ _) hc
    · exact CZeroLift.exists_cZero_of_symThree _ (hatHom_surjective _ _ hX)
        (isPGroup_ker_hatHom _ _ hX) (pCore_hat_eq_bot _ _) hT.1 hb
  obtain ⟨I, hI, rfl⟩ := hlift
  refine map_mono fun x hx => ?_
  rw [mem_subgroupOf] at hx ⊢
  exact (le_iSup₂ (f := fun I (_ : I ∈ cZero (H ⊓ L)) => I) I hI) hx

theorem map_barHom_subgroupOf {M X L : Subgroup G} (hXL : X ≤ L) (hL : L ≤ M) :
    (X.subgroupOf L).map (barHom M L hL) = (barM M X).subgroupOf (barM M L) := by
  ext y
  rw [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨inclusion hL x, hx, rfl⟩
  · rintro ⟨m, hm, hmy⟩
    refine ⟨⟨m, hXL hm⟩, hm, Subtype.ext ?_⟩
    rw [coe_barHom, ← hmy]
    rfl

theorem relIndex_eq_relIndex_barM {M X L : Subgroup G} (hXL : X ≤ L) (hL : L ≤ M)
    (hk : L ⊓ pCoreOf 2 M ≤ X) : X.relIndex L = (barM M X).relIndex (barM M L) := by
  rw [relIndex, relIndex, ← map_barHom_subgroupOf hXL hL]
  refine (index_map_eq _ (barHom_surjective M L hL) fun x hx => ?_).symm
  rw [mem_subgroupOf]
  exact hk ⟨x.2, mem_ker_barHom.mp hx⟩

theorem not_two_dvd_relIndex_jZero {M H L : Subgroup G} (hL : L ≤ M)
    (hk : L ⊓ pCoreOf 2 M ≤ H) (h1 : ¬ 2 ∣ (barM M (H ⊓ L)).relIndex (barM M L))
    (h2 : ¬ 2 ∣ (wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)))).index) :
    ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L := by
  have hXL : H ⊓ L ≤ L := inf_le_right
  have hXM : H ⊓ L ≤ M := hXL.trans hL
  set X := H ⊓ L with hXdef
  set N := jZero H L ⊔ pCoreOf 2 X with hNdef
  have hNX : N ≤ X := sup_le (jZero_le H L) (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  rw [← relIndex_mul_relIndex N X L hNX hXL,
    relIndex_eq_relIndex_barM hXL hL (fun x hx => ⟨hk hx, hx.1⟩)]
  have hker : (hatHom M X hXM).ker ≤ N.subgroupOf X := by
    intro x hx
    rw [mem_subgroupOf]
    refine mem_sup_right ?_
    rw [pCoreOf_eq_map_ker M X hXM]
    exact ⟨x, hx, rfl⟩
  have hNi : N.relIndex X = ((N.subgroupOf X).map (hatHom M X hXM)).index :=
    (index_map_eq _ (hatHom_surjective M X hXM) hker).symm
  have hW : wSup (↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X)) ≤
      (N.subgroupOf X).map (hatHom M X hXM) :=
    (wSup_le_map_jZero M H L hXM).trans (map_mono fun x hx => by
      rw [mem_subgroupOf] at hx ⊢
      exact mem_sup_left hx)
  have hdvd := index_dvd_of_le hW
  rw [hNi]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
  · exact h2 (h'.trans hdvd)
  · exact h1 h'

theorem conj_mem_barM {M X : Subgroup G} {g : G} (hg : g ∈ M)
    (hgX : g ∈ normalizer (X : Set G)) {y : ↥M ⧸ CFSG.pCore 2 ↥M} (hy : y ∈ barM M X) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩ * y *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩)⁻¹ ∈ barM M X := by
  obtain ⟨m, hm, rfl⟩ := hy
  refine ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  have hm' : (m : G) ∈ X := hm
  show ((⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹ : ↥M) : G) ∈ X
  simpa using (mem_normalizer_iff.mp hgX m).mp hm'

theorem mem_normalizer_barM {M X : Subgroup G} {g : G} (hg : g ∈ M)
    (hgX : g ∈ normalizer (X : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩ ∈ normalizer (barM M X : Set _) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_barM hg hgX hy, fun hy => ?_⟩
  have h := conj_mem_barM (inv_mem hg) (inv_mem hgX) hy
  have e : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g⁻¹, inv_mem hg⟩ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e] at h
  simpa [mul_assoc] using h

theorem barHom_mem_pCoreOf {M X : Subgroup G} (hX : X ≤ M) {x : ↥X} (hx : (x : G) ∈ pCoreOf 2 X) :
    ((barHom M X hX x : ↥(barM M X)) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ pCoreOf 2 (barM M X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (CFSG.pCore 2 ↥X).map (barHom M X hX) ≤ CFSG.pCore 2 ↥(barM M X) :=
    le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := ↥X)).map _ (barHom_surjective M X hX),
      (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map _⟩
  obtain ⟨x', hx', hxx'⟩ := hx
  have : x' = x := Subtype.ext hxx'
  subst this
  exact ⟨_, hle ⟨x', hx', rfl⟩, rfl⟩

theorem pCoreOf_jZero_le (H L : Subgroup G) : pCoreOf 2 (jZero H L) ≤ pCoreOf 2 (H ⊓ L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (jZero_le H L)) (fun x hx => ?_)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
    (le_normalizer_jZero H L (le_normalizer hx))

theorem commutator_mem_of_wSup {M H L : Subgroup G} (hX : H ⊓ L ≤ M) {b : G} (hb : b ∈ M)
    (hbX : b ∈ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hbJ : ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))
    {w : ↥M ⧸ CFSG.pCore 2 ↥M} (hw : w ∈ barM M (H ⊓ L))
    (hwW : QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M (H ⊓ L))) ⟨w, hw⟩ ∈
      wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)))) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * w *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩)⁻¹ * w⁻¹ ∈ pCoreOf 2 (barM M (H ⊓ L)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := barM M (H ⊓ L) with hP
  set bb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ with hbb
  have hbP := mem_normalizer_barM (X := H ⊓ L) hb hbX
  have hbO : bb ∈ normalizer (pCoreOf 2 P : Set _) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P hbP
  have hPO : ∀ y ∈ P, y ∈ normalizer (pCoreOf 2 P : Set _) := fun y hy =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (le_normalizer hy)
  obtain ⟨j, hj0, hjw⟩ := (wSup_le_map_jZero M H L hX) hwW
  have hj : (j : G) ∈ jZero H L := hj0
  have hjw' : (barHom M (H ⊓ L) hX j)⁻¹ * ⟨w, hw⟩ ∈ CFSG.pCore 2 ↥P := by
    have h := hjw
    rw [hatHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h
    exact h
  set u : ↥M ⧸ CFSG.pCore 2 ↥M := ((barHom M (H ⊓ L) hX j : ↥P) : ↥M ⧸ CFSG.pCore 2 ↥M)
    with hu
  have huP : u ∈ P := (barHom M (H ⊓ L) hX j).2
  set o : ↥M ⧸ CFSG.pCore 2 ↥M := u⁻¹ * w with ho
  have hoO : o ∈ pCoreOf 2 P := ⟨_, hjw', by simp [ho, hu]⟩
  have hwuo : w = u * o := by rw [ho]; group
  have hc : b * (j : G) * b⁻¹ * (j : G)⁻¹ ∈ H ⊓ L :=
    (pCoreOf_jZero_le H L).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (hbJ _ hj)
  have hcX : b * (j : G) * b⁻¹ * (j : G)⁻¹ ∈ pCoreOf 2 (H ⊓ L) := pCoreOf_jZero_le H L (hbJ _ hj)
  have hcbar := barHom_mem_pCoreOf hX (x := ⟨_, hc⟩) hcX
  have hcomm : bb * u * bb⁻¹ * u⁻¹ =
      ((barHom M (H ⊓ L) hX ⟨_, hc⟩ : ↥P) : ↥M ⧸ CFSG.pCore 2 ↥M) := by
    rw [coe_barHom, hu, coe_barHom, hbb]
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have h1 : bb * u * bb⁻¹ * u⁻¹ ∈ pCoreOf 2 P := by rw [hcomm]; exact hcbar
  have h2 : bb * o * bb⁻¹ * o⁻¹ ∈ pCoreOf 2 P :=
    mul_mem ((mem_normalizer_iff.mp hbO o).mp hoO) (inv_mem hoO)
  have h3 : u * (bb * o * bb⁻¹ * o⁻¹) * u⁻¹ ∈ pCoreOf 2 P :=
    (mem_normalizer_iff.mp (hPO u huP) _).mp h2
  have e : bb * w * bb⁻¹ * w⁻¹ =
      (bb * u * bb⁻¹ * u⁻¹) * (u * (bb * o * bb⁻¹ * o⁻¹) * u⁻¹) := by
    rw [hwuo]; group
  rw [e]
  exact mul_mem h1 h3

theorem commutator_mem_pCoreOf_of_centralizes {M L : Subgroup G} (hL : L ≤ M) {b : G}
    (hb : b ∈ M) (hc : ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩) :
    ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M := by
  intro l hl
  have h := hc _ ⟨⟨l, hL hl⟩, hl, rfl⟩
  have h' : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      (⟨b, hb⟩ * ⟨l, hL hl⟩ * ⟨b, hb⟩⁻¹ * ⟨l, hL hl⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
  exact ⟨_, h', rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

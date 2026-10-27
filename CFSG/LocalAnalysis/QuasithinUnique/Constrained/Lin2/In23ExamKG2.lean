module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKElem
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatG2
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog
open scoped commutatorElement

namespace G2Exam

section Core

variable {F : Type} [Field F]

local notation "X" => pinnedX Tag.G2 F

theorem g2r_mem
    (s : F) : X g2r s ∈ posUnipotent Tag.G2 F := by
  rw [pinnedX_r_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _

theorem g2a_mem
    (s : F) : X g2a s ∈ posUnipotent Tag.G2 F := by
  rw [pinnedX_a_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _

theorem g2v_mem
    (s : F) : X g2v s ∈ posUnipotent Tag.G2 F := by
  rw [pinnedX_v_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _

theorem g2b_mem
    (s : F) : X g2b s ∈ posUnipotent Tag.G2 F := by
  rw [pinnedX_b_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _

theorem X_b_mul_X_c_eq_one
    {e f : F} (h : X g2b e * X g2c f = 1) : e = 0 ∧ f = 0 := by
  have h' : g2N 0 0 0 0 e f = g2N 0 0 0 0 0 0 := by
    rw [g2N_zero, ← h]
    simp only [g2N, pinnedX_zero, one_mul]
  obtain ⟨-, -, -, -, he, hf⟩ := g2N_injective h'
  exact ⟨he, hf⟩

theorem g2_short_false
    [CharP F 2] {R₁ A₁ A₁' : Subgroup (ModGL Tag.G2 F)}
    (hnorm : ∀ n ∈ adjointGroup Tag.G2 F,
      n ∈ Subgroup.normalizer (posUnipotent Tag.G2 F : Set (ModGL Tag.G2 F)) →
        ∀ r ∈ R₁, n * r * n⁻¹ ∈ R₁)
    (hstrong : ∀ r ∈ R₁, r * r = 1 → ∀ g ∈ adjointGroup Tag.G2 F,
      g * r * g⁻¹ ∈ posUnipotent Tag.G2 F → g * r * g⁻¹ ∈ R₁)
    (hA : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a) (hA' : ∀ a ∈ A₁', ∀ b ∈ A₁', a * b = b * a)
    (hel : ∀ e ∈ R₁, e * e = 1 → e ∈ A₁ ∨ e ∈ A₁')
    {s : F} (hs : s ≠ 0) (hu : X g2u s ∈ R₁) : False := by
  have _ := hnorm
  have hr : X g2r s ∈ R₁ := by
    have hn : weylElt Tag.G2 F g2ia 1 * X g2r s * (weylElt Tag.G2 F g2ia 1)⁻¹ = X g2u s := by
      rw [weylElt_conj g2ia isRoot_g2r, reflect_a_r]
    have e : (weylElt Tag.G2 F g2ia 1)⁻¹ * X g2u s * (weylElt Tag.G2 F g2ia 1)⁻¹⁻¹ = X g2r s := by
      rw [← hn]; group
    have := hstrong (X g2u s) hu (pinnedX_mul_self _ _) (weylElt Tag.G2 F g2ia 1)⁻¹
      (Subgroup.inv_mem _ (weylElt_mem_adjointGroup _ _)) (by rw [e]; exact g2r_mem s)
    rwa [e] at this
  have hv : X g2v s ∈ R₁ := by
    have hn : weylElt Tag.G2 F g2ir 1 * X g2u s * (weylElt Tag.G2 F g2ir 1)⁻¹ = X g2v s := by
      rw [weylElt_conj g2ir isRoot_g2u, reflect_r_u]
    have := hstrong (X g2u s) hu (pinnedX_mul_self _ _) (weylElt Tag.G2 F g2ir 1)
      (weylElt_mem_adjointGroup _ _) (by rw [hn]; exact g2v_mem s)
    rwa [hn] at this
  refine three_noncommuting hA hA' (hel _ hr (pinnedX_mul_self _ _)) (hel _ hu (pinnedX_mul_self _ _))
    (hel _ hv (pinnedX_mul_self _ _)) ?_ ?_ ?_
  ·
    intro hc
    have h1 : ⁅X g2r s, X g2u s⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
    rw [comm_r_u] at h1
    rw [← (commute_b_c (s ^ 2 * s) (s * s ^ 2)).eq] at h1
    obtain ⟨h2, -⟩ := X_b_mul_X_c_eq_one h1
    exact (mul_ne_zero (pow_ne_zero 2 hs) hs) h2
  · intro hc
    have h1 : ⁅X g2r s, X g2v s⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
    rw [comm_r_v] at h1
    have h2 : s * s = 0 :=
      pinnedX_injective Tag.G2 F g2b (h1.trans (pinnedX_zero Tag.G2 F g2b).symm)
    exact hs (mul_self_eq_zero.mp h2)
  · intro hc
    have h1 : ⁅X g2u s, X g2v s⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
    rw [comm_u_v] at h1
    have h2 : s * s = 0 :=
      pinnedX_injective Tag.G2 F g2c (h1.trans (pinnedX_zero Tag.G2 F g2c).symm)
    exact hs (mul_self_eq_zero.mp h2)

theorem g2_center_form
    [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F) {z : ModGL Tag.G2 F}
    (hz : z ∈ posUnipotent Tag.G2 F)
    (hc : ∀ (α : Fin Tag.G2.rank → ℤ) (s : F), X α s ∈ posUnipotent Tag.G2 F →
      X α s * z * X α s = z) : ∃ F₀ : F, z = X g2c F₀ := by
  obtain ⟨A, B, C, D, E, F', hzN⟩ := exists_g2N_of_mem_posUnipotent hz
  subst hzN
  have hr : ∀ s : F, X g2r s * g2N A B C D E F' * X g2r s = g2N A B C D E F' := fun s =>
    hc g2r s (g2r_mem s)
  have ha : ∀ s : F, X g2a s * g2N A B C D E F' * X g2a s = g2N A B C D E F' := fun s =>
    hc g2a s (g2a_mem s)
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := CFSG.QuasithinUnique.K1.g2N_center hF4 hr ha
  exact ⟨F', by rw [pinnedX_c_eq_g2N]⟩

theorem g2_exists_short
    [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F) {R₁ : Subgroup (ModGL Tag.G2 F)}
    (hnorm : ∀ n ∈ adjointGroup Tag.G2 F,
      n ∈ Subgroup.normalizer (posUnipotent Tag.G2 F : Set (ModGL Tag.G2 F)) →
        ∀ r ∈ R₁, n * r * n⁻¹ ∈ R₁)
    (hstrong : ∀ r ∈ R₁, r * r = 1 → ∀ g ∈ adjointGroup Tag.G2 F,
      g * r * g⁻¹ ∈ posUnipotent Tag.G2 F → g * r * g⁻¹ ∈ R₁)
    {F₀ : F} (hF₀ : F₀ ≠ 0) (hz : X g2c F₀ ∈ R₁) : ∃ s : F, s ≠ 0 ∧ X g2u s ∈ R₁ := by
  obtain ⟨ω, hω0, hω1⟩ := CFSG.QuasithinUnique.K1.exists_ne_zero_one hF4
  have hpos : ∀ q ∈ posUnipotent Tag.G2 F, ∀ r ∈ R₁, q * r * q⁻¹ ∈ R₁ := fun q hq r hr =>
    hnorm q (posUnipotent_le_adjointGroup hq) (Subgroup.le_normalizer hq) r hr
  have htor : ∀ (i : Fin Tag.G2.rank) (t : Fˣ), ∀ r ∈ R₁,
      torusElt Tag.G2 F i t * r * (torusElt Tag.G2 F i t)⁻¹ ∈ R₁ := fun i t r hr =>
    hnorm _ (torusElt_mem_adjointGroup _ _)
      (torusGroup_le_normalizer_posUnipotent (torusElt_mem_torusGroup _ _)) r hr
  have hc1 : X g2c 1 ∈ R₁ := by
    have := htor g2ia (Units.mk0 F₀ hF₀)⁻¹ _ hz
    rw [torus_a_c, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hF₀] at this
    exact this
  have hb1 : X g2b 1 ∈ R₁ := by
    have hn : weylElt Tag.G2 F g2ia 1 * X g2b 1 * (weylElt Tag.G2 F g2ia 1)⁻¹ = X g2c 1 := by
      rw [weylElt_conj g2ia isRoot_g2b, reflect_a_b]
    have e : (weylElt Tag.G2 F g2ia 1)⁻¹ * X g2c 1 * (weylElt Tag.G2 F g2ia 1)⁻¹⁻¹ = X g2b 1 := by
      rw [← hn]; group
    have := hstrong (X g2c 1) hc1 (pinnedX_mul_self _ _) (weylElt Tag.G2 F g2ia 1)⁻¹
      (Subgroup.inv_mem _ (weylElt_mem_adjointGroup _ _)) (by rw [e]; exact g2b_mem 1)
    rwa [e] at this
  have ha1 : X g2a 1 ∈ R₁ := by
    have hn : weylElt Tag.G2 F g2ir 1 * X g2a 1 * (weylElt Tag.G2 F g2ir 1)⁻¹ = X g2b 1 := by
      rw [weylElt_conj g2ir isRoot_g2a, reflect_r_a]
    have e : (weylElt Tag.G2 F g2ir 1)⁻¹ * X g2b 1 * (weylElt Tag.G2 F g2ir 1)⁻¹⁻¹ = X g2a 1 := by
      rw [← hn]; group
    have := hstrong (X g2b 1) hb1 (pinnedX_mul_self _ _) (weylElt Tag.G2 F g2ir 1)⁻¹
      (Subgroup.inv_mem _ (weylElt_mem_adjointGroup _ _)) (by rw [e]; exact g2a_mem 1)
    rwa [e] at this
  have hw : X g2u 1 * X g2v 1 * X g2b 1 * X g2c 1 ∈ R₁ := by
    have h1 := hpos _ (g2r_mem 1) _ ha1
    have h2 : X g2r 1 * X g2a 1 * (X g2r 1)⁻¹ * (X g2a 1)⁻¹ ∈ R₁ :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ha1)
    have h3 : ⁅X g2a 1, X g2r 1⁆ = X g2u 1 * X g2v 1 * X g2b 1 * X g2c 1 := by
      rw [comm_a_r]; simp
    have h4 : ⁅X g2a 1, X g2r 1⁆ = (X g2r 1 * X g2a 1 * (X g2r 1)⁻¹ * (X g2a 1)⁻¹)⁻¹ := by
      rw [← commutatorElement_inv, commutatorElement_def]
    rw [← h3, h4]
    exact Subgroup.inv_mem _ h2
  have huv : X g2u 1 * X g2v 1 ∈ R₁ := by
    have e : X g2u 1 * X g2v 1 = (X g2u 1 * X g2v 1 * X g2b 1 * X g2c 1) * (X g2c 1)⁻¹ *
        (X g2b 1)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hc1))
      (Subgroup.inv_mem _ hb1)
  set t : Fˣ := Units.mk0 ω hω0 with ht
  have hu1 : torusElt Tag.G2 F g2ia t * X g2u 1 * (torusElt Tag.G2 F g2ia t)⁻¹ = X g2u ω := by
    rw [root_torus_conjugation g2ia isRoot_g2u t 1]
    have hs : ∑ j, Tag.G2.cartan g2ia j * g2u j = 1 := by decide
    rw [hs, zpow_one, ht, Units.val_mk0, mul_one]
  have hv1 : torusElt Tag.G2 F g2ia t * X g2v 1 * (torusElt Tag.G2 F g2ia t)⁻¹ = X g2v 1 := by
    rw [root_torus_conjugation g2ia isRoot_g2v t 1]
    have hs : ∑ j, Tag.G2.cartan g2ia j * g2v j = 0 := by decide
    rw [hs, zpow_zero, Units.val_one, mul_one]
  have huvω : X g2u ω * X g2v 1 ∈ R₁ := by
    have := htor g2ia t _ huv
    have e : torusElt Tag.G2 F g2ia t * (X g2u 1 * X g2v 1) * (torusElt Tag.G2 F g2ia t)⁻¹ =
        (torusElt Tag.G2 F g2ia t * X g2u 1 * (torusElt Tag.G2 F g2ia t)⁻¹) *
          (torusElt Tag.G2 F g2ia t * X g2v 1 * (torusElt Tag.G2 F g2ia t)⁻¹) := by group
    rwa [e, hu1, hv1] at this
  have hs0 : ω + 1 ≠ 0 := by
    intro h
    exact hω1 (by linear_combination h - CharTwo.two_eq_zero (R := F))
  refine ⟨ω + 1, hs0, ?_⟩
  have e : X g2u (ω + 1) = (X g2u ω * X g2v 1) * (X g2u 1 * X g2v 1)⁻¹ := by
    have h1 : (X g2u 1 * X g2v 1)⁻¹ = X g2v 1 * X g2u 1 := by
      rw [mul_inv_rev, pinnedX_inv_eq, pinnedX_inv_eq]
    rw [h1, pinnedX_add]
    calc X g2u ω * X g2u 1 = X g2u ω * (X g2v 1 * X g2v 1) * X g2u 1 := by
          rw [pinnedX_mul_self, mul_one]
      _ = X g2u ω * X g2v 1 * (X g2v 1 * X g2u 1) := by group
  rw [e]
  exact Subgroup.mul_mem _ huvω (Subgroup.inv_mem _ huv)

end Core

theorem g2_false
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F)
    (R₀ A₀ A₀' : Subgroup (adjointGroup Tag.G2 F))
    (hRU : R₀ ≤ (posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F))
    (hU : IsSylowTwoOf ((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) ⊤)
    (hnorm : ∀ n ∈ Subgroup.normalizer
      (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) : Subgroup _) : Set _),
        ∀ r ∈ R₀, n * r * n⁻¹ ∈ R₀)
    (hne : R₀ ≠ ⊥) (hA : IsElemAbelian 2 A₀) (hA' : IsElemAbelian 2 A₀')
    (hel : ∀ e ∈ R₀, e * e = 1 → e ∈ A₀ ∨ e ∈ A₀')
    (hstrong : ∀ r ∈ R₀, r * r = 1 → ∀ g : adjointGroup Tag.G2 F,
      g * r * g⁻¹ ∈ (posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) →
        g * r * g⁻¹ ∈ R₀) : False := by
  have hQ2 : IsPGroup 2 ↥((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) := hU.2.1
  obtain ⟨z, hzR, hz1, hzc⟩ := CFSG.QuasithinUnique.K1.exists_ne_one_mem_centralizer hQ2 hRU
    (fun a ha q hq => by
      have := hnorm q⁻¹ (Subgroup.le_normalizer (Subgroup.inv_mem _ hq)) a ha
      simpa using this) hne
  have hzU : (z : ModGL Tag.G2 F) ∈ posUnipotent Tag.G2 F := Subgroup.mem_subgroupOf.mp (hRU hzR)
  have hconj : ∀ (α : Fin Tag.G2.rank → ℤ) (s : F), pinnedX Tag.G2 F α s ∈ posUnipotent Tag.G2 F →
      pinnedX Tag.G2 F α s * (z : ModGL Tag.G2 F) * pinnedX Tag.G2 F α s = (z : ModGL Tag.G2 F) := by
    intro α s hαU
    have hmem : (⟨pinnedX Tag.G2 F α s, pinnedX_mem_adjointGroup α s⟩ : adjointGroup Tag.G2 F) ∈
        (posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) := hαU
    have h := congrArg Subtype.val (hzc _ hmem)
    simp only [Subgroup.coe_mul] at h
    calc pinnedX Tag.G2 F α s * (z : ModGL Tag.G2 F) * pinnedX Tag.G2 F α s
        = (z : ModGL Tag.G2 F) * pinnedX Tag.G2 F α s * pinnedX Tag.G2 F α s := by rw [h]
      _ = (z : ModGL Tag.G2 F) := by rw [mul_assoc, pinnedX_mul_self, mul_one]
  obtain ⟨F₀, hF₀⟩ := g2_center_form hF4 hzU hconj
  have hF₀0 : F₀ ≠ 0 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    rw [hF₀, pinnedX_zero]
    rfl
  let ι : adjointGroup Tag.G2 F →* ModGL Tag.G2 F := (adjointGroup Tag.G2 F).subtype
  have hnorm₁ : ∀ n ∈ adjointGroup Tag.G2 F,
      n ∈ Subgroup.normalizer (posUnipotent Tag.G2 F : Set (ModGL Tag.G2 F)) →
        ∀ r ∈ R₀.map ι, n * r * n⁻¹ ∈ R₀.map ι := by
    intro n hn hnn r hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hn' : (⟨n, hn⟩ : adjointGroup Tag.G2 F) ∈ Subgroup.normalizer
        (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) : Subgroup _) : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have := Subgroup.mem_normalizer_iff.mp hnn (y : ModGL Tag.G2 F)
      exact this
    exact ⟨⟨n, hn⟩ * x * ⟨n, hn⟩⁻¹, hnorm _ hn' x hx, rfl⟩
  have hstrong₁ : ∀ r ∈ R₀.map ι, r * r = 1 → ∀ g ∈ adjointGroup Tag.G2 F,
      g * r * g⁻¹ ∈ posUnipotent Tag.G2 F → g * r * g⁻¹ ∈ R₀.map ι := by
    intro r hr hrr g hg hgU
    obtain ⟨x, hx, rfl⟩ := hr
    have hxx : x * x = 1 := Subtype.ext hrr
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hstrong x hx hxx ⟨g, hg⟩ hgU, rfl⟩
  have hel₁ : ∀ e ∈ R₀.map ι, e * e = 1 → e ∈ A₀.map ι ∨ e ∈ A₀'.map ι := by
    intro e he hee
    obtain ⟨x, hx, rfl⟩ := he
    have hxx : x * x = 1 := Subtype.ext hee
    rcases hel x hx hxx with h | h
    · exact Or.inl ⟨x, h, rfl⟩
    · exact Or.inr ⟨x, h, rfl⟩
  have hcomm : ∀ {B : Subgroup (adjointGroup Tag.G2 F)}, IsElemAbelian 2 B →
      ∀ a ∈ B.map ι, ∀ b ∈ B.map ι, a * b = b * a := by
    intro B hB a ha b hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have := hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg (fun w : B => ((w : adjointGroup Tag.G2 F) : ModGL Tag.G2 F)) this
  obtain ⟨s, hs, hu⟩ := g2_exists_short hF4 hnorm₁ hstrong₁ hF₀0
    (hF₀ ▸ ⟨z, hzR, rfl⟩ : pinnedX Tag.G2 F g2c F₀ ∈ R₀.map ι)
  exact g2_short_false hnorm₁ hstrong₁ (hcomm hA) (hcomm hA') hel₁ hs hu

theorem _root_.CFSG.QuasithinUnique.Lin2.examExcludes_g2
    : ExamExcludes FamG2 := by
  rintro G _ _ K B B' P R m h ⟨f, hf, hmodel⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcp : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  let e' : ↥K ⧸ Subgroup.center ↥K ≃* adjointGroup Tag.G2 F :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  let θ : ↥K →* adjointGroup Tag.G2 F :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθsurj : Function.Surjective θ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : θ.ker ≤ Subgroup.center ↥K := by
    intro x hx
    have hx' : e' (QuotientGroup.mk x) = 1 := hx
    rwa [map_eq_one_iff e' e'.injective, QuotientGroup.eq_one_iff] at hx'
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.G2).length
  obtain ⟨⟨P', hP'⟩, -⟩ := exceptional_ordinary_Sylow_opposition Tag.G2 F 2 w₀ hw₀
  have hU : IsSylowTwoOf ((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) ⊤ := by
    rw [← hP']
    exact CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨P'.isPGroup', P'.not_dvd_index⟩
  obtain ⟨R₀, A₀, A₀', hRU, hnorm, hne, hA, hA', hel, hstrong⟩ :=
    h.toAbs.exists_RprimeE θ hθsurj hker _ hU
  exact g2_false hF4 R₀ A₀ A₀' hRU hU hnorm hne hA hA' hel hstrong

end G2Exam

end CFSG.QuasithinUnique.Lin2

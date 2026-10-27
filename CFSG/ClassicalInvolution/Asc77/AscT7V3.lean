module

public import CFSG.ClassicalInvolution.Asc77.AscT7V2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

namespace Ctx

variable (c : Ctx p f Ω W)
include c

theorem exists_relation (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W)
    (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) :
    ∃ (σ : Rep Ω W) (t : G) (g : Fin 4 → G), IsUniqueInvolution σ.K t ∧
      (∀ i, σ.img * (ρ i).img ≠ (ρ i).img * σ.img) ∧
      (∀ i, g i ∈ (ρ i).K ⊓ W ∧ orderOf (g i) = 4) ∧ t = g 0 * g 1 * g 2 * g 3 := by
  classical
  have hP : PartIHyp p f Ω := ⟨c.hp, c.hq, c.hΩ, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hp c.hq c.hΩ c.hW (thompsonCube G Ω hP W c.hW)
  have hS : Star3T.IsStar (muDelta Ω W) :=
    isStar_muDelta c.hp c.hq c.hΩ c.hW (thompsonStar G Ω hP W c.hW)
  obtain ⟨rep, hrep⟩ : ∃ rep : ↥(muGroup Ω W) → Rep Ω W,
      ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)) := by
    have hex : ∀ x ∈ muDelta Ω W, ∃ ρ : Rep Ω W, ρ.img = (x : NQuot (W ⊔ OCW W)) :=
      fun x hx => exists_rep_of_mem_muDelta hx
    have : Nonempty (Rep Ω W) := ⟨ρ 0⟩
    choose! rep hrep using hex
    exact ⟨rep, hrep⟩
  set x : Fin 4 → ↥(muGroup Ω W) := fun i => T7D.imgQ (ρ i) with hx
  have hxΔ : ∀ i, x i ∈ muDelta Ω W := fun i => T7D.imgQ_mem (ρ i)
  have hne_of : ∀ σ σ' : Rep Ω W, σ.K ≠ σ'.K → T7D.imgQ σ ≠ T7D.imgQ σ' := fun σ σ' hK e =>
    hK (c.K_eq_of_img_eq σ σ' (congrArg Subtype.val e))
  have hcomm_of : ∀ σ σ' : Rep Ω W, σ'.K ∈ omegaNbr Ω σ.K →
      T7D.imgQ σ * T7D.imgQ σ' = T7D.imgQ σ' * T7D.imgQ σ := fun σ σ' h =>
    Subtype.ext (c.comm_of_omega σ σ' h)
  have hxne : ∀ i j, i ≠ j → x i ≠ x j := fun i j hij => hne_of _ _ (hne i j hij)
  have hxC : ∀ i, x i ∈ Star3T.cent (muDelta Ω W) (x 0) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact Star3T.self_mem_cent (hxΔ 0)
    · exact ⟨hxΔ i, (hcomm_of (ρ 0) (ρ i) (hnbr 0 i (Ne.symm hi))).symm⟩
  have hxC' : ({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hxne 0 1 (by decide), hxne 0 2 (by decide),
        hxne 0 3 (by decide)]),
      Finset.card_insert_of_notMem (by simp [hxne 1 2 (by decide), hxne 1 3 (by decide)]),
      Finset.card_insert_of_notMem (by simp [hxne 2 3 (by decide)]), Finset.card_singleton]
  have hC4 : (Star3T.cent (muDelta Ω W) (x 0)).ncard = 4 := by
    have hsub : (↑({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)) : Set ↥(muGroup Ω W)) ⊆
        Star3T.cent (muDelta Ω W) (x 0) := by
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxC 0
      · exact hxC 1
      · exact hxC 2
      · exact hxC 3
    have hge : 4 ≤ (Star3T.cent (muDelta Ω W) (x 0)).ncard := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_coe_finset, hxC'] at this
    rcases thompsonClique G Ω hP W c.hW hnc (x 0) (hxΔ 0) with h | h | ⟨h, -⟩
    · omega
    · omega
    · exact h
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ := exists_not_conn_of_not_connected c.hp c.hq c.hΩ c.hW hnc
  obtain ⟨a, haΔ, hna⟩ : ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) (x 0) a := by
    by_cases h : Star3T.Conn (muDelta Ω W) (x 0) d₀
    · exact ⟨a₀, ha₀, fun h' => hn₀ (h.symm.trans h')⟩
    · exact ⟨d₀, hd₀, h⟩
  have hcfg : Star3T.Cfg (muDelta Ω W) (x 0) a := ⟨hTT, hS, hxΔ 0, haΔ, hna⟩
  obtain ⟨n, B, hcard, hBC, hdB, hBn, hgen⟩ := hcfg.exists_generating_family
  have hn : n = 2 := by
    have h4 : 2 ^ n = 2 ^ 2 := by rw [← hcard, hC4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h4
  have hB3 : B.card = 3 := by rw [hBn, hn]
  obtain ⟨P, hP', hPB⟩ : ∃ P ∈ Star3T.cent (muDelta Ω W) (x 0), P ∉ B := by
    by_contra hall
    push Not at hall
    have h1 : (Star3T.cent (muDelta Ω W) (x 0)).ncard ≤ B.card := by
      calc (Star3T.cent (muDelta Ω W) (x 0)).ncard ≤ (↑B : Set ↥(muGroup Ω W)).ncard :=
            Set.ncard_le_ncard (fun P hP => Finset.mem_coe.mpr (hall P hP)) (Set.toFinite _)
        _ = B.card := Set.ncard_coe_finset B
    omega
  have hsub := c.clique_subset rep hrep hcfg hBC hdB hgen hP' hPB
  obtain ⟨za, g, hza, hmem, hrel⟩ := c.clique_relation' rep hrep hcfg hBC hdB hgen hP' hPB hB3
  have hcardPB : (insert P B).card = 4 := by rw [Finset.card_insert_of_notMem hPB, hB3]
  have hSeq : ({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)) = insert P B := by
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [hxC', hcardPB])
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have hyC : y ∈ Star3T.cent (muDelta Ω W) (x 0) := by
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxC 0
      · exact hxC 1
      · exact hxC 2
      · exact hxC 3
    by_cases hyP : y = P
    · rw [hyP]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hsub y hyC hyP)
  have hKeq : ∀ i, (rep (x i)).K = (ρ i).K := fun i =>
    c.K_eq_of_img_eq (rep (x i)) (ρ i) (hrep (x i) (hxΔ i))
  have hxmem : ∀ i, x i ∈ insert P B := fun i => by
    rw [← hSeq]
    fin_cases i <;> simp [hx]
  refine ⟨rep a, za, fun i => g (x i), hza, ?_, ?_, ?_⟩
  · intro i hcomm
    apply hna
    have h1 : a * x i = x i * a := by
      apply Subtype.ext
      have := hrep a haΔ
      have h2 : (rep a).img * (ρ i).img = (ρ i).img * (rep a).img := hcomm
      rw [this] at h2
      exact h2
    obtain ⟨-, hAON⟩ := c.clique_dichotomy hnc (hxΔ 0)
    have : a ∈ Star3T.cent (muDelta Ω W) (x 0) := hAON a haΔ (x i) (hxC i) h1
    exact Star3T.conn_of_mem_cent (hxΔ 0) this
  · intro i
    have := hmem (x i) (hxmem i)
    rw [hKeq i] at this
    exact this
  · exact hrel (x 0) (x 1) (x 2) (x 3) (hxne 0 1 (by decide)) (hxne 0 2 (by decide))
      (hxne 0 3 (by decide)) (hxne 1 2 (by decide)) (hxne 1 3 (by decide))
      (hxne 2 3 (by decide)) hSeq

theorem rep_le_centralizer (ρ : Rep Ω W) {y : G} (hy : y ∈ W) (hr : ρ.r * y = y * ρ.r) :
    ρ.R ≤ Subgroup.centralizer ({y} : Set G) := by
  obtain ⟨-, -, -, -, hcard⟩ := inf_W_of_mem_D c.hp c.hq c.hΩ c.hW ρ.hR ρ.hK ρ.hRK
  have hidx : ((ρ.R ⊓ W).subgroupOf ρ.R).index = 2 :=
    relIndex_eq_two_of_card inf_le_left hcard
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  have : ((ρ.R ⊓ W).subgroupOf ρ.R).Normal := Subgroup.normal_of_index_eq_two hidx
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hxW : x ∈ W
  · exact c.comm_W x hxW y hy
  · have hb : (⟨x, hx⟩ : ↥ρ.R) ∉ (ρ.R ⊓ W).subgroupOf ρ.R := fun h =>
      hxW (Subgroup.mem_subgroupOf.mp h).2
    have hb' : (⟨ρ.r, ρ.hr⟩ : ↥ρ.R) ∉ (ρ.R ⊓ W).subgroupOf ρ.R := fun h =>
      ρ.hrW (Subgroup.mem_subgroupOf.mp h).2
    have h1 : (⟨x, hx⟩ : ↥ρ.R) * a ∈ (ρ.R ⊓ W).subgroupOf ρ.R := by
      rcases ha ⟨x, hx⟩ with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hb
    have h2 : (⟨ρ.r, ρ.hr⟩ : ↥ρ.R) * a ∈ (ρ.R ⊓ W).subgroupOf ρ.R := by
      rcases ha ⟨ρ.r, ρ.hr⟩ with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hb'
    have h3 : (⟨ρ.r, ρ.hr⟩ : ↥ρ.R)⁻¹ * ⟨x, hx⟩ ∈ (ρ.R ⊓ W).subgroupOf ρ.R := by
      have h4 : (a⁻¹ * (⟨ρ.r, ρ.hr⟩ : ↥ρ.R)⁻¹ * ⟨x, hx⟩ * a) ∈ (ρ.R ⊓ W).subgroupOf ρ.R := by
        have := ((ρ.R ⊓ W).subgroupOf ρ.R).mul_mem (((ρ.R ⊓ W).subgroupOf ρ.R).inv_mem h2) h1
        simpa [mul_assoc] using this
      have h5 := ‹((ρ.R ⊓ W).subgroupOf ρ.R).Normal›.conj_mem _ h4 a
      simpa [mul_assoc] using h5
    have hW3 : ρ.r⁻¹ * x ∈ W := (Subgroup.mem_subgroupOf.mp h3).2
    have hcomm : (ρ.r⁻¹ * x) * y = y * (ρ.r⁻¹ * x) := c.comm_W _ hW3 y hy
    calc x * y = ρ.r * ((ρ.r⁻¹ * x) * y) := by group
      _ = ρ.r * (y * (ρ.r⁻¹ * x)) := by rw [hcomm]
      _ = (ρ.r * y) * (ρ.r⁻¹ * x) := by group
      _ = (y * ρ.r) * (ρ.r⁻¹ * x) := by rw [hr]
      _ = y * x := by group

theorem conjRep_braid (ρ σ : Rep Ω W) (hnc : ρ.img * σ.img ≠ σ.img * ρ.img)
    (hn : ρ.r * σ.r * ρ.r⁻¹ ∈ Subgroup.normalizer (W : Set G)) :
    (T7D.conjRep c.hΩ hn ρ).img = σ.img := by
  have hP : PartIHyp p f Ω := ⟨c.hp, c.hq, c.hΩ, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hp c.hq c.hΩ c.hW (thompsonCube G Ω hP W c.hW)
  have hdΔ := T7D.imgQ_mem ρ
  have hsΔ := T7D.imgQ_mem σ
  have hdd := hTT.mul_self _ hdΔ
  have hss := hTT.mul_self _ hsΔ
  have hbr := hTT.braid hdΔ hsΔ (fun e => hnc (congrArg Subtype.val e))
  have hdi := hTT.inv_eq hdΔ
  have hsi := hTT.inv_eq hsΔ
  set d : ↥(muGroup Ω W) := T7D.imgQ ρ with hd
  set s : ↥(muGroup Ω W) := T7D.imgQ σ with hs
  have key : (d * s * d⁻¹) * d * (d * s * d⁻¹)⁻¹ = s := by
    have hinv : (d * s * d⁻¹)⁻¹ = d * s * d := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hdi, hsi]
      group
    rw [hinv, hdi]
    calc d * s * d * d * (d * s * d) = d * s * (d * d) * (d * s * d) := by group
      _ = (d * s * d) * (s * d) := by rw [hdd]; group
      _ = (s * d * s) * (s * d) := by rw [hbr]
      _ = s * d * (s * s) * d := by group
      _ = s := by rw [hss]; calc s * d * 1 * d = s * (d * d) := by group
                                _ = s := by rw [hdd]; group
  have hρr := ρ.r_mem_normalizer
  have hσr := σ.r_mem_normalizer
  have hpn : Thompson.piG W (ρ.r * σ.r * ρ.r⁻¹) = ((d * s * d⁻¹ : ↥(muGroup Ω W)) :
      NQuot (W ⊔ OCW W)) := by
    rw [Thompson.piG_mul (Subgroup.mul_mem _ hρr hσr) (Subgroup.inv_mem _ hρr),
      Thompson.piG_mul hρr hσr, Thompson.piG_inv hρr]
    rfl
  rw [T7D.conjRep_img, hpn]
  exact congrArg Subtype.val key

theorem far_conj (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) (σ : Rep Ω W)
    (hfar : ∀ i, σ.img * (ρ i).img ≠ (ρ i).img * σ.img)
    (hn : (ρ 0).r ∈ Subgroup.normalizer (W : Set G)) :
    ∀ i, (T7D.conjRep c.hΩ hn σ).img * (ρ i).img ≠
      (ρ i).img * (T7D.conjRep c.hΩ hn σ).img := by
  have hP : PartIHyp p f Ω := ⟨c.hp, c.hq, c.hΩ, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hp c.hq c.hΩ c.hW (thompsonCube G Ω hP W c.hW)
  obtain ⟨hcl, hAON⟩ := c.clique_dichotomy hnc (T7D.imgQ_mem (ρ 0))
  have hxC : ∀ i, T7D.imgQ (ρ i) ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ (ρ 0)) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact Star3T.self_mem_cent (T7D.imgQ_mem (ρ 0))
    · exact ⟨T7D.imgQ_mem (ρ i), (Subtype.ext (c.comm_of_omega (ρ 0) (ρ i)
        (hnbr 0 i (Ne.symm hi)))).symm⟩
  intro i hcomm
  set x₀ : ↥(muGroup Ω W) := T7D.imgQ (ρ 0) with hx₀
  set s : ↥(muGroup Ω W) := T7D.imgQ σ with hs
  have hx₀Δ := T7D.imgQ_mem (ρ 0)
  have hsΔ := T7D.imgQ_mem σ
  have hx₀₀ := hTT.mul_self _ hx₀Δ
  have hx₀i := hTT.inv_eq hx₀Δ
  have hs'Δ : x₀ * s * x₀⁻¹ ∈ muDelta Ω W := hTT.conj_mem s hsΔ x₀
  have hs'img : (T7D.conjRep c.hΩ hn σ).img = ((x₀ * s * x₀⁻¹ : ↥(muGroup Ω W)) :
      NQuot (W ⊔ OCW W)) := by
    rw [T7D.conjRep_img]
    have : Thompson.piG W (ρ 0).r = (x₀ : NQuot (W ⊔ OCW W)) := rfl
    rw [this]
    rfl
  have hcomm' : (x₀ * s * x₀⁻¹) * T7D.imgQ (ρ i) = T7D.imgQ (ρ i) * (x₀ * s * x₀⁻¹) := by
    apply Subtype.ext
    rw [hs'img] at hcomm
    exact hcomm
  have hin : x₀ * s * x₀⁻¹ ∈ Star3T.cent (muDelta Ω W) x₀ :=
    hAON _ hs'Δ _ (hxC i) hcomm'
  have h1 : (x₀ * s * x₀⁻¹) * x₀ = x₀ * (x₀ * s * x₀⁻¹) := hin.2
  apply hfar 0
  have h2 : s * x₀ = x₀ * s := by
    have h3 : x₀ * s = x₀ * x₀ * s * x₀⁻¹ := by
      calc x₀ * s = (x₀ * s * x₀⁻¹) * x₀ := by group
        _ = x₀ * (x₀ * s * x₀⁻¹) := h1
        _ = x₀ * x₀ * s * x₀⁻¹ := by group
    rw [hx₀₀, one_mul] at h3
    rw [hx₀i] at h3
    exact h3.symm
  exact congrArg Subtype.val h2

theorem fuse_frame (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W) {z : G}
    (hz : ∀ i, IsUniqueInvolution (ρ i).K z)
    (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) :
    ∃ (σ : Rep Ω W) (t : G) (g : Fin 4 → G), IsUniqueInvolution σ.K t ∧
      (∀ i, σ.img * (ρ i).img ≠ (ρ i).img * σ.img) ∧
      (∀ i, g i ∈ (ρ i).K ⊓ W ∧ orderOf (g i) = 4) ∧ t = g 0 * g 1 * g 2 * g 3 ∧
      σ.R ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
  classical
  obtain ⟨σ, t, g, ht, hfar, hg, hrel⟩ := c.exists_relation hnc ρ hne hnbr
  have hgsq : ∀ i, g i * g i = z := fun i =>
    sq_eq_involution_of_orderOf_four (hz i) (hg i).1.1 (hg i).2
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hz2 : z * z = 1 := (hz 0).sq
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution (ρ 0) (hz 0)
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution σ ht
  have hKσ : ∀ i, σ.K ≠ (ρ i).K := fun i h => hfar i (by rw [c.img_eq_of_K_eq σ (ρ i) h])
  have hnot : ∀ i, (ρ i).K ∉ omegaNbr Ω σ.K := fun i h => hfar i (c.comm_of_omega σ (ρ i) h)
  have hnot' : ∀ i, σ.K ∉ omegaNbr Ω (ρ i).K := fun i h => hfar i
    (c.comm_of_omega (ρ i) σ h).symm
  have hτz : σ.r * z * σ.r⁻¹ = t * z := c.conj_involution σ (ρ 0) (hKσ 0) (hnot 0) ht (hz 0)
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hrW : ∀ x ∈ W, σ.r * x * σ.r⁻¹ ∈ W := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp σ.r_mem_normalizer x).mp hx
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → G, ∀ i, e i = σ.r * g i * σ.r⁻¹ * (g i)⁻¹ := ⟨_, fun _ => rfl⟩
  have heW : ∀ i, e i ∈ σ.K ⊓ W := fun i => by
    rw [he]; exact c.comm_mem σ (ρ i) (hKσ i) (hg i).1
  have hegi : ∀ i, σ.r * g i * σ.r⁻¹ = e i * g i := fun i => by rw [he]; group
  have hesq : ∀ i, e i * e i = t := by
    intro i
    have hw : σ.r * g i * σ.r⁻¹ ∈ W := hrW _ (hgW i)
    have h1 : (σ.r * g i * σ.r⁻¹) * (σ.r * g i * σ.r⁻¹) = t * z := by
      calc (σ.r * g i * σ.r⁻¹) * (σ.r * g i * σ.r⁻¹) = σ.r * (g i * g i) * σ.r⁻¹ := by group
        _ = t * z := by rw [hgsq i, hτz]
    have hgi : (g i)⁻¹ ∈ W := W.inv_mem (hgW i)
    have h2 : (g i)⁻¹ * (g i)⁻¹ = z := by
      have : (g i)⁻¹ * (g i)⁻¹ = (g i * g i)⁻¹ := by group
      rw [this, hgsq i]
      exact inv_eq_of_mul_eq_one_right hz2
    calc e i * e i = (σ.r * g i * σ.r⁻¹) * (σ.r * g i * σ.r⁻¹) * ((g i)⁻¹ * (g i)⁻¹) := by
          rw [he]
          have := hcomm _ hw _ hgi
          calc σ.r * g i * σ.r⁻¹ * (g i)⁻¹ * (σ.r * g i * σ.r⁻¹ * (g i)⁻¹)
              = σ.r * g i * σ.r⁻¹ * ((g i)⁻¹ * (σ.r * g i * σ.r⁻¹)) * (g i)⁻¹ := by group
            _ = σ.r * g i * σ.r⁻¹ * ((σ.r * g i * σ.r⁻¹) * (g i)⁻¹) * (g i)⁻¹ := by rw [this]
            _ = _ := by group
      _ = t := by rw [h1, h2, mul_assoc, hz2, mul_one]
  have hht : t * t = 1 := ht.sq
  have hcase : e 1 = e 0 ∨ e 1 = (e 0)⁻¹ := by
    have hsq : (e 1 * (e 0)⁻¹) * (e 1 * (e 0)⁻¹) = 1 := by
      have hc := hcomm _ (heW 1).2 _ (W.inv_mem (heW 0).2)
      calc (e 1 * (e 0)⁻¹) * (e 1 * (e 0)⁻¹) = e 1 * ((e 0)⁻¹ * e 1) * (e 0)⁻¹ := by group
        _ = e 1 * (e 1 * (e 0)⁻¹) * (e 0)⁻¹ := by rw [← hc]
        _ = (e 1 * e 1) * ((e 0)⁻¹ * (e 0)⁻¹) := by group
        _ = t * t := by
            rw [hesq 1]
            congr 1
            have : (e 0)⁻¹ * (e 0)⁻¹ = (e 0 * e 0)⁻¹ := by group
            rw [this, hesq 0]
            exact inv_eq_of_mul_eq_one_right hht
        _ = 1 := hht
    have hmem : e 1 * (e 0)⁻¹ ∈ σ.K := σ.K.mul_mem (heW 1).1 (σ.K.inv_mem (heW 0).1)
    rcases ht.unique _ hmem hsq with h | h
    · left
      calc e 1 = (e 1 * (e 0)⁻¹) * e 0 := by group
        _ = e 0 := by rw [h, one_mul]
    · right
      have hinv : (e 0)⁻¹ = e 0 * t := by
        have : e 0 * (e 0 * t) = 1 := by
          rw [← mul_assoc, hesq 0, hht]
        exact inv_eq_of_mul_eq_one_right this
      calc e 1 = (e 1 * (e 0)⁻¹) * e 0 := by group
        _ = t * e 0 := by rw [h]
        _ = e 0 * t := hcomm _ htW _ (heW 0).2
        _ = (e 0)⁻¹ := hinv.symm
  rcases hcase with hB | hA
  ·
    have hr₀ : (ρ 0).r ∈ Subgroup.normalizer (W : Set G) := (ρ 0).r_mem_normalizer
    have hne0 : (ρ 0).K ≠ σ.K := fun h => hKσ 0 h.symm
    have hτ' : (ρ 0).r * t * (ρ 0).r⁻¹ = z * t :=
      c.conj_involution (ρ 0) σ hne0 (hnot' 0) (hz 0) ht
    refine ⟨T7D.conjRep c.hΩ hr₀ σ, (ρ 0).r * t * (ρ 0).r⁻¹,
      fun i => if i = 2 then (g 2)⁻¹ else g i, ht.conj _,
      c.far_conj hnc ρ hnbr σ hfar hr₀, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = 2
      · subst hi
        simp only [ite_true]
        exact ⟨⟨(ρ 2).K.inv_mem (hg 2).1.1, W.inv_mem (hgW 2)⟩, by rw [orderOf_inv]; exact (hg 2).2⟩
      · simp only [hi, ite_false]
        exact hg i
    · have h20 : ¬ ((0 : Fin 4) = 2) := by decide
      have h21 : ¬ ((1 : Fin 4) = 2) := by decide
      have h23 : ¬ ((3 : Fin 4) = 2) := by decide
      simp only [h20, h21, h23, ite_false, ite_true]
      rw [hτ', hrel]
      have hWc : ∀ x y : ↥W, x * y = y * x := fun x y => Subtype.ext (hcomm x x.2 y y.2)
      let _ : CommGroup ↥W := { (inferInstance : Group ↥W) with mul_comm := hWc }
      have h2 : (⟨g 2, hgW 2⟩ : ↥W)⁻¹ = ⟨g 2, hgW 2⟩ * ⟨z, hzW⟩ := by
        apply inv_eq_of_mul_eq_one_right
        rw [← mul_assoc]
        apply Subtype.ext
        show g 2 * g 2 * z = 1
        rw [hgsq 2, hz2]
      have hgoal : (⟨z, hzW⟩ : ↥W) * (⟨g 0, hgW 0⟩ * ⟨g 1, hgW 1⟩ * ⟨g 2, hgW 2⟩ * ⟨g 3, hgW 3⟩) =
          ⟨g 0, hgW 0⟩ * ⟨g 1, hgW 1⟩ * (⟨g 2, hgW 2⟩)⁻¹ * ⟨g 3, hgW 3⟩ := by
        rw [h2]
        ac_rfl
      exact congrArg Subtype.val hgoal
    · have h20 : ¬ ((0 : Fin 4) = 2) := by decide
      have h21 : ¬ ((1 : Fin 4) = 2) := by decide
      simp only [h20, h21, ite_false]
      have hy : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
      refine c.rep_le_centralizer (T7D.conjRep c.hΩ hr₀ σ) hy ?_
      have hr₀g₀ : (ρ 0).r * g 0 * (ρ 0).r⁻¹ = (g 0)⁻¹ := c.conj_inv (ρ 0) (hg 0).1
      have hr₀g₁ : (ρ 0).r * g 1 = g 1 * (ρ 0).r :=
        c.centralizes (ρ 0) (ρ 1) (hnbr 0 1 (by decide)) (hg 1).1
      have hr₀g₁' : (ρ 0).r * g 1 * (ρ 0).r⁻¹ = g 1 := by rw [hr₀g₁]; group
      have hinv₀ : (ρ 0).r⁻¹ * g 0 * (ρ 0).r = (g 0)⁻¹ := by
        have h3 : (ρ 0).r⁻¹ * (g 0)⁻¹ * (ρ 0).r = g 0 := by
          calc (ρ 0).r⁻¹ * (g 0)⁻¹ * (ρ 0).r = (ρ 0).r⁻¹ * ((ρ 0).r * g 0 * (ρ 0).r⁻¹) *
              (ρ 0).r := by rw [hr₀g₀]
            _ = g 0 := by group
        calc (ρ 0).r⁻¹ * g 0 * (ρ 0).r = ((ρ 0).r⁻¹ * (g 0)⁻¹ * (ρ 0).r)⁻¹ := by group
          _ = (g 0)⁻¹ := by rw [h3]
      have hinv₁ : (ρ 0).r⁻¹ * g 1 * (ρ 0).r = g 1 := by
        calc (ρ 0).r⁻¹ * g 1 * (ρ 0).r = (ρ 0).r⁻¹ * (g 1 * (ρ 0).r) := by group
          _ = (ρ 0).r⁻¹ * ((ρ 0).r * g 1) := by rw [hr₀g₁]
          _ = g 1 := by group
      have h1 : ((ρ 0).r * σ.r * (ρ 0).r⁻¹) * (g 0 * g 1) * ((ρ 0).r * σ.r * (ρ 0).r⁻¹)⁻¹ =
          g 0 * g 1 := by
        calc ((ρ 0).r * σ.r * (ρ 0).r⁻¹) * (g 0 * g 1) * ((ρ 0).r * σ.r * (ρ 0).r⁻¹)⁻¹
            = (ρ 0).r * (σ.r * ((ρ 0).r⁻¹ * g 0 * (ρ 0).r) * ((ρ 0).r⁻¹ * g 1 * (ρ 0).r) *
                σ.r⁻¹) * (ρ 0).r⁻¹ := by group
          _ = (ρ 0).r * ((σ.r * g 0 * σ.r⁻¹)⁻¹ * (σ.r * g 1 * σ.r⁻¹)) * (ρ 0).r⁻¹ := by
              rw [hinv₀, hinv₁]; group
          _ = (ρ 0).r * ((e 0 * g 0)⁻¹ * (e 1 * g 1)) * (ρ 0).r⁻¹ := by rw [hegi 0, hegi 1]
          _ = (ρ 0).r * ((e 0 * g 0)⁻¹ * (e 0 * g 1)) * (ρ 0).r⁻¹ := by rw [hB]
          _ = (ρ 0).r * ((g 0)⁻¹ * g 1) * (ρ 0).r⁻¹ := by group
          _ = ((ρ 0).r * g 0 * (ρ 0).r⁻¹)⁻¹ * ((ρ 0).r * g 1 * (ρ 0).r⁻¹) := by group
          _ = g 0 * g 1 := by rw [hr₀g₀, hr₀g₁', inv_inv]
      exact mul_inv_eq_iff_eq_mul.mp h1
  ·
    refine ⟨σ, t, g, ht, hfar, hg, hrel, ?_⟩
    have hy : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
    refine c.rep_le_centralizer σ hy ?_
    have h1 : σ.r * (g 0 * g 1) * σ.r⁻¹ = g 0 * g 1 := by
      calc σ.r * (g 0 * g 1) * σ.r⁻¹ = (σ.r * g 0 * σ.r⁻¹) * (σ.r * g 1 * σ.r⁻¹) := by group
        _ = (e 0 * g 0) * (e 1 * g 1) := by rw [hegi 0, hegi 1]
        _ = (e 0 * g 0) * ((e 0)⁻¹ * g 1) := by rw [hA]
        _ = (g 0 * e 0) * ((e 0)⁻¹ * g 1) := by rw [hcomm _ (heW 0).2 _ (hgW 0)]
        _ = g 0 * (e 0 * (e 0)⁻¹) * g 1 := by group
        _ = g 0 * g 1 := by group
    exact (mul_inv_eq_iff_eq_mul.mp h1)

end Ctx

end Thompson

end CFSG.ClassicalInvolution.Asc77

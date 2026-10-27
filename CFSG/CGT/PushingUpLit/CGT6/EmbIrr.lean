module

public import CFSG.CGT.PushingUpLit.CGT6.EmbQuotCfg

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Fixed

theorem exists_fixed_of_hom {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    [Nontrivial W] {Q : Type} [Group Q] (hQ : IsPGroup 2 Q) (ρ : Q →* MulAut W) :
    ∃ w : W, w ≠ 1 ∧ ∀ q : Q, ρ q w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction Q W := MulAction.compHom W ρ
  have hmod := hQ.card_modEq_card_fixedPoints W
  have hWp : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := W)).mp hWp
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : Nat.card W = 1 := by simpa using hk
    have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial W)
    have h3 : 1 < Nat.card W := by simpa [Nat.card_eq_fintype_card] using h2
    omega
  have h2W : 2 ∣ Nat.card W := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have hdvd : 2 ∣ Nat.card (MulAction.fixedPoints Q W) :=
    (Nat.ModEq.dvd_iff hmod (dvd_refl 2)).mp h2W
  let x0 : MulAction.fixedPoints Q W := ⟨1, fun q => by show ρ q 1 = 1; exact map_one _⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints Q W) := by
    have : Nonempty (MulAction.fixedPoints Q W) := ⟨x0⟩
    exact Nat.card_pos
  have hgt : 1 < Nat.card (MulAction.fixedPoints Q W) := by
    obtain ⟨m, hm⟩ := hdvd
    omega
  have : Nontrivial (MulAction.fixedPoints Q W) := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨x, hx⟩ := exists_ne x0
  refine ⟨x.1, fun h => hx (Subtype.ext h), fun q => ?_⟩
  exact x.2 q

end Fixed

section FixV

variable {V : Type} [CommGroup V] [Finite V]

theorem fixV_eq_bot_of_cfg (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (cfg : Emb4Cfg G T Y) : fixV G = ⊥ := by
  by_contra hne
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  let A : Subgroup V := Subgroup.zpowers a
  have hfix : ∀ g ∈ G, ∀ x ∈ A, g x = x := by
    intro g hg x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [map_zpow, ha g hg]
  have hcard : Nat.card ↥A ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num)
      (orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hV a))
  have hO2 : oTwoIn G = ⊥ := by
    show (pCore 2 ↥G).map G.subtype = ⊥
    rw [cfg.o2, Subgroup.map_bot]
  have D : QData G A := QData.of_oTwoIn_eq_bot hV hfix hcard hO2
  have hA : A ≠ ⊥ := by
    intro h
    apply ha1'
    have : a ∈ A := Subgroup.mem_zpowers a
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hVb : ∀ v : V ⧸ A, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H v =>
      rw [← QuotientGroup.mk_pow, hV v]
      rfl
  obtain ⟨Xb, hXb⟩ := cfg.ih (V ⧸ A) hVb (barQ D.inv G) (D.smaller hA)
    (isKGroup_barQ D cfg.kgroup) (barQ D.inv T) (barQ D.inv Y) (D.adm4_barQ hV cfg.adm)
  exact cfg.nolift (D.lift_of_bar hV cfg hXb)

end FixV

section Irr

variable {V : Type} [CommGroup V] [Finite V]

theorem commV_le_of_inv (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (cfg : Emb4Cfg G T Y) (hfix : fixV G = ⊥) {B : Subgroup V} (hB : GInv G B) (hB1 : B ≠ ⊥) :
    commV Y ≤ B := by
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hTG : T ≤ G := cfg.adm.hTG
  have hperf := cfg.adm.hperf
  have hPerf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  by_cases hcase : B ⊓ commV Y ≤ fixV Y
  · exfalso
    have hBY : GInv Y B := fun y hy b hb => hB y (hYG hy) b hb
    have hYB : ∀ (y : ↥Y) (b : ↥B), (y : MulAut V) (b : V) = (b : V) := by
      have h := trivial_of_unipotent (resG Y B hBY) ((fixV Y).subgroupOf B)
        (fun g a ha => Subtype.ext ((mem_fixV.mp ha) g g.2))
        (fun g v => by
          rw [Subgroup.mem_subgroupOf]
          exact hcase ⟨B.mul_mem (hB g (hYG g.2) v v.2) (B.inv_mem v.2),
            commV_mem_of_apply Y g v⟩)
      intro y b
      exact congrArg Subtype.val (h y b)
    have hLB : conjClosure Y G ≤ fixW B := by
      rw [conjClosure, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, hy, rfl⟩ b hb
      have h1 : g⁻¹ b ∈ B := hB g⁻¹ (G.inv_mem hg) b hb
      have h2 : y (g⁻¹ b) = g⁻¹ b := hYB ⟨y, hy⟩ ⟨g⁻¹ b, h1⟩
      show (g * y * g⁻¹) b = b
      simp only [MulAut.mul_apply]
      rw [h2]
      simp
    have hBT : GInv T B := fun t ht b hb => hB t (hTG ht) b hb
    have hVB : ∀ w : ↥B, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
    have : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB1
    obtain ⟨b, hb1, hb⟩ := exists_fixed_of_hom hVB cfg.adm.hT2 (resG T B hBT)
    have hstab : G ≤ MulAction.stabilizer (MulAut V) (b : V) := by
      rw [← cfg.gen]
      refine sup_le (fun l hl => ?_) (fun t ht => ?_)
      · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hLB hl b b.2
      · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact congrArg Subtype.val (hb ⟨t, ht⟩)
    have hbG : (b : V) ∈ fixV G := fun g hg => by
      have := MulAction.mem_stabilizer_iff.mp (hstab hg)
      rwa [MulAut.smul_def] at this
    rw [hfix, Subgroup.mem_bot] at hbG
    exact hb1 (Subtype.ext hbG)
  ·
    set N : Subgroup V := (B ⊓ commV Y) ⊔ (commV Y ⊓ fixV Y) with hN
    have hNinv : ∀ g ∈ Y, ∀ n ∈ N, g n ∈ N := by
      intro g hg n hn
      obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ := Subgroup.mem_sup.mp hn
      rw [map_mul, (mem_fixV.mp hn₂.2) g hg]
      exact mul_mem (Subgroup.mem_sup_left ⟨hB g (hYG hg) n₁ hn₁.1, commV_invariant hg hn₁.2⟩)
        (Subgroup.mem_sup_right hn₂)
    have hNU : N ≤ commV Y := sup_le inf_le_right inf_le_left
    rcases ClassX4.invariant_irreducible hperf hV cfg.adm.hcls N hNinv hNU le_sup_right with h | h
    · exact absurd (fun x hx => (h ▸ Subgroup.mem_sup_left hx : x ∈ commV Y ⊓ fixV Y).2) hcase
    · refine (USelf_of_perfect hperf) B (fun g hg u hu => ?_)
      rw [← h] at hu
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul, (mem_fixV.mp hu₂.2) g hg]
      have : (g : MulAut V) u₁ * u₂ * (u₁ * u₂)⁻¹ = (g : MulAut V) u₁ * u₁⁻¹ := by group
      rw [this]
      exact B.mul_mem (hB g (hYG hg) u₁ hu₁.1) (B.inv_mem hu₁.1)

theorem irr_of_cfg (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (cfg : Emb4Cfg G T Y) : ∀ B : Subgroup V, GInv G B → B = ⊥ ∨ B = ⊤ := by
  intro B hB
  by_cases hB1 : B = ⊥
  · exact Or.inl hB1
  right
  by_contra hBtop
  have hfix := fixV_eq_bot_of_cfg hV cfg
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hTG : T ≤ G := cfg.adm.hTG
  have hUB : commV Y ≤ B := commV_le_of_inv hV cfg hfix hB hB1
  let S : Set (Subgroup V) := {M | GInv G M ∧ B ≤ M ∧ M ≠ ⊤}
  obtain ⟨M, hMS, hMmax⟩ := Set.Finite.exists_maximalFor (fun M : Subgroup V => M) S
    (Set.toFinite S) ⟨B, hB, le_rfl, hBtop⟩
  obtain ⟨hMinv, hBM, hMtop⟩ := hMS
  have hUM : commV Y ≤ M := hUB.trans hBM
  have hLM : conjClosure Y G ≤ trivQ M := by
    refine conjClosure_le_trivQ fun g hg y hy v => ?_
    rw [conj_mul_apply]
    exact hMinv g hg _ (hUM (Subgroup.subset_closure ⟨y, hy, g⁻¹ v, rfl⟩))
  have hnt : Nontrivial (V ⧸ M) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hMtop
    rw [eq_top_iff]
    intro v _
    have : (v : V ⧸ M) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff v).mp this
  have hVb : ∀ w : V ⧸ M, w ^ 2 = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H v =>
      rw [← QuotientGroup.mk_pow, hV v]
      rfl
  obtain ⟨c', hc1, hc⟩ := exists_fixed_of_hom hVb cfg.adm.hT2
    ((resQ G M hMinv).comp (Subgroup.inclusion hTG))
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c'
  have hcM : c ∉ M := fun h => hc1 ((QuotientGroup.eq_one_iff c).mpr h)
  have hTc : ∀ t ∈ T, t c * c⁻¹ ∈ M := by
    intro t ht
    have h1 := hc ⟨t, ht⟩
    have h2 : (((t : MulAut V) c : V) : V ⧸ M) = (c : V ⧸ M) := h1
    have h3 := M.inv_mem (QuotientGroup.eq.mp h2)
    rwa [mul_inv_rev, inv_inv, mul_comm] at h3
  have hLc : ∀ l ∈ conjClosure Y G, l c * c⁻¹ ∈ M := fun l hl => hLM hl c
  have hGc : ∀ g ∈ G, g c * c⁻¹ ∈ M := by
    have hLG : conjClosure Y G ≤ G := conjClosure_le hYG
    have key : ∀ g ∈ conjClosure Y G ⊔ T, g ∈ G ∧ g c * c⁻¹ ∈ M := by
      intro g hg
      rw [Subgroup.sup_eq_closure] at hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · exact ⟨hLG hx, hLc x hx⟩
        · exact ⟨hTG hx, hTc x hx⟩
      | one => exact ⟨G.one_mem, by simp⟩
      | mul x y _ _ hx hy =>
        refine ⟨G.mul_mem hx.1 hy.1, ?_⟩
        have : (x * y) c * c⁻¹ = x (y c * c⁻¹) * (x c * c⁻¹) := by
          simp only [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [this]
        exact M.mul_mem (hMinv x hx.1 _ hy.2) hx.2
      | inv x _ hx =>
        refine ⟨G.inv_mem hx.1, ?_⟩
        have : x⁻¹ c * c⁻¹ = (x⁻¹ (x c * c⁻¹))⁻¹ := by
          have h1 : x⁻¹ (x c) = c := by simp [MulAut.inv_apply]
          rw [map_mul, map_inv, h1]
          group
        rw [this]
        exact M.inv_mem (hMinv x⁻¹ (G.inv_mem hx.1) _ hx.2)
    intro g hg
    rw [← cfg.gen] at hg
    exact (key g hg).2
  have hinv' : GInv G (M ⊔ Subgroup.zpowers c) := by
    intro g hg m hm
    obtain ⟨m₁, hm₁, z, hz, rfl⟩ := Subgroup.mem_sup.mp hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_mul, map_zpow]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (hMinv g hg m₁ hm₁))
      (Subgroup.zpow_mem _ ?_ k)
    have : g c = (g c * c⁻¹) * c := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hGc g hg))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hM'top : M ⊔ Subgroup.zpowers c = ⊤ := by
    by_contra hne
    have hmem : M ⊔ Subgroup.zpowers c ∈ S := ⟨hinv', hBM.trans le_sup_left, hne⟩
    have hle := hMmax hmem le_sup_left
    exact hcM (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)))
  have hcomm : commV G ≤ M := by
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, v, rfl⟩
    have hv : v ∈ M ⊔ Subgroup.zpowers c := by
      rw [hM'top]
      exact Subgroup.mem_top v
    obtain ⟨m₁, hm₁, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have : g (m₁ * c ^ k) * (m₁ * c ^ k)⁻¹ = (g m₁ * m₁⁻¹) * (g c * c⁻¹) ^ k := by
      simp only [map_mul, map_zpow, mul_zpow, mul_inv_rev, inv_zpow]
      ac_rfl
    show g (m₁ * c ^ k) * (m₁ * c ^ k)⁻¹ ∈ M
    rw [this]
    exact M.mul_mem (M.mul_mem (hMinv g hg m₁ hm₁) (M.inv_mem hm₁))
      (Subgroup.zpow_mem _ (hGc g hg) k)
  rw [cfg.comm] at hcomm
  exact hMtop (top_le_iff.mp hcomm)

end Irr

end CFSG.CGT.PushingUpLit.CGT6

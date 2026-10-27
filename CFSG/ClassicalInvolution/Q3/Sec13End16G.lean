module

public import CFSG.ClassicalInvolution.Q3.Sec13End16N
public import CFSG.ClassicalInvolution.Q3.Sec13PerpW

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

private theorem e16g1_conjSub_sup (x : G) (A B : Subgroup G) :
    conjSub x (A ⊔ B) = conjSub x A ⊔ conjSub x B :=
  Subgroup.map_sup _ _ _

private theorem e16g1_conjSub_inf (x : G) (A B : Subgroup G) :
    conjSub x (A ⊓ B) = conjSub x A ⊓ conjSub x B :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective

private theorem e16g1_mem_centerIn {R : Subgroup G} {y : G} :
    y ∈ Asc77.centerIn R ↔ y ∈ R ∧ ∀ r ∈ R, r * y = y * r := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun r hr => ?_⟩
    have := (Subgroup.mem_center_iff.mp hc) ⟨r, hr⟩
    exact congrArg Subtype.val this
  · rintro ⟨hy, hc⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)

private theorem e16g1_centerIn_conj (x : G) (W : Subgroup G) :
    conjSub x (Asc77.centerIn (Subgroup.normalizer (W : Set G))) =
      Asc77.centerIn (Subgroup.normalizer ((conjSub x W : Subgroup G) : Set G)) := by
  have hN : ∀ n : G, n ∈ Subgroup.normalizer ((conjSub x W : Subgroup G) : Set G) ↔
      x⁻¹ * n * x ∈ Subgroup.normalizer (W : Set G) := by
    intro n
    have key : conjSub n (conjSub x W) = conjSub x (conjSub (x⁻¹ * n * x) W) := by
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    rw [mem_normalizer_iff_conjSub_eq, mem_normalizer_iff_conjSub_eq, key,
      (conjSub_injective x).eq_iff]
  have hcomm : ∀ y r : G, r * y = y * r ↔
      x⁻¹ * r * x * (x⁻¹ * y * x) = x⁻¹ * y * x * (x⁻¹ * r * x) := by
    intro y r
    constructor
    · intro hr
      calc x⁻¹ * r * x * (x⁻¹ * y * x) = x⁻¹ * (r * y) * x := by group
        _ = x⁻¹ * (y * r) * x := by rw [hr]
        _ = x⁻¹ * y * x * (x⁻¹ * r * x) := by group
    · intro hr
      have h1 : x⁻¹ * (r * y) * x = x⁻¹ * (y * r) * x := by
        calc x⁻¹ * (r * y) * x = x⁻¹ * r * x * (x⁻¹ * y * x) := by group
          _ = x⁻¹ * y * x * (x⁻¹ * r * x) := hr
          _ = x⁻¹ * (y * r) * x := by group
      exact mul_left_cancel (mul_right_cancel h1)
  ext y
  rw [mem_conjSub_iff, e16g1_mem_centerIn, e16g1_mem_centerIn, hN y]
  refine and_congr Iff.rfl ⟨fun hc r hr => ?_, fun hc s hs => ?_⟩
  · exact (hcomm y r).mpr (hc _ ((hN r).mp hr))
  · have hr : x * s * x⁻¹ ∈ Subgroup.normalizer ((conjSub x W : Subgroup G) : Set G) := by
      rw [hN, show x⁻¹ * (x * s * x⁻¹) * x = s by group]
      exact hs
    have h1 := (hcomm y (x * s * x⁻¹)).mp (hc _ hr)
    rwa [show x⁻¹ * (x * s * x⁻¹) * x = s by group] at h1

private theorem e16g1_twinSet_congr {A B : Subgroup G} {z : G} (hA : IsUniqueInvolution A z)
    (hB : IsUniqueInvolution B z) : twinSet Ω A = twinSet Ω B := by
  ext J
  simp only [twinSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hJ, w, hw, hJw⟩
    have hwz : w = z := (hA.eq hw).symm
    rw [hwz] at hJw
    exact ⟨hJ, z, hB, hJw⟩
  · rintro ⟨hJ, w, hw, hJw⟩
    have hwz : w = z := (hB.eq hw).symm
    rw [hwz] at hJw
    exact ⟨hJ, z, hA, hJw⟩

private theorem e16g1_dSet_conj (h : EndHyp Ω) {R W : Subgroup G} (hR : R ∈ DSet Ω W) (x : G) :
    conjSub x R ∈ DSet Ω (conjSub x W) := by
  rw [h.mem_dSet_iff] at hR ⊢
  refine ⟨h.thmD.hyp.conjInvariant x R hR.1, fun y hy => ?_⟩
  rw [mem_normalizer_iff_conjSub_eq]
  have hr : x⁻¹ * y * x ∈ R := mem_conjSub_iff.mp hy
  have hN : conjSub (x⁻¹ * y * x) W = W := mem_normalizer_iff_conjSub_eq.mp (hR.2 hr)
  calc conjSub y (conjSub x W) = conjSub (y * x) W := (conjSub_mul y x W).symm
    _ = conjSub (x * (x⁻¹ * y * x)) W := by congr 1; group
    _ = conjSub x (conjSub (x⁻¹ * y * x) W) := conjSub_mul _ _ _
    _ = conjSub x W := by rw [hN]

private theorem e16g1_eq_of_mem_closure {a b : G} (ha : a * a = 1) (hb1 : b ≠ 1)
    (hb : b ∈ Subgroup.closure ({a} : Set G)) : b = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_closure_singleton.mp hb
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [zpow_mul, ha2, one_zpow] at hb1
    exact absurd rfl hb1
  · rw [zpow_add_one, zpow_mul, ha2, one_zpow, one_mul]

theorem symm (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) : Sit16 Ω K' K W z u e g := by
  have s := c.twin
  have hK' : TwinSit Ω K' K z := by
    refine ⟨s.mem_twin.1, s.mem_twin.2, ?_, s.ne.symm⟩
    rw [e16g1_twinSet_congr s.mem_twin.2 s.isInv, s.twin, Set.pair_comm]
  refine ⟨hK', { c.data with hu := by rw [sup_comm]; exact c.data.hu }, ?_⟩
  rw [sup_comm]
  exact c.e_not_mem

theorem conjG (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (x : G) :
    Sit16 Ω (conjSub x K) (conjSub x K') (conjSub x W) (x * z * x⁻¹) (x * u * x⁻¹)
      (x * e * x⁻¹) (x * g * x⁻¹) := by
  have hΩ := h.thmD.hyp.conjInvariant
  have hd := c.data
  have hS4 : MuIsoS4 Ω (conjSub x W) := by
    obtain ⟨e₀⟩ := hd.hS4
    exact ⟨(TL4.muGroupConjEquivGen h.thmD.hyp x W).symm.trans e₀⟩
  have hu : x * u * x⁻¹ ∈ conjSub x K ⊔ conjSub x K' := by
    rw [← e16g1_conjSub_sup]
    exact conj_mem_conjSub hd.hu
  have hu1 : x * u * x⁻¹ ≠ 1 := by
    intro h1
    apply hd.hu1
    have := congrArg (fun t => x⁻¹ * t * x) h1
    simpa [mul_assoc] using this
  have huz : x * u * x⁻¹ ≠ x * z * x⁻¹ :=
    fun h1 => hd.huz (mul_left_cancel (mul_right_cancel h1))
  have hu2 : x * u * x⁻¹ * (x * u * x⁻¹) = 1 := by
    calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
      _ = 1 := by rw [hd.hu2]; group
  have he1 : x * e * x⁻¹ ≠ 1 := by
    intro h1
    apply hd.he1
    have := congrArg (fun t => x⁻¹ * t * x) h1
    simpa [mul_assoc] using this
  have he2 : x * e * x⁻¹ * (x * e * x⁻¹) = 1 := by
    calc x * e * x⁻¹ * (x * e * x⁻¹) = x * (e * e) * x⁻¹ := by group
      _ = 1 := by rw [hd.he2]; group
  have he : Subgroup.closure ({x * e * x⁻¹} : Set G) =
      conjSub x W ⊓ Asc77.centerIn (Subgroup.normalizer ((conjSub x W : Subgroup G) : Set G)) := by
    have h1 : Subgroup.closure ({x * e * x⁻¹} : Set G) = conjSub x (Subgroup.closure {e}) := by
      rw [conjSub, MonoidHom.map_closure]
      congr 1
      simp [MulAut.conj_apply]
    rw [h1, hd.he, e16g1_conjSub_inf, e16g1_centerIn_conj]
  have hg : x * g * x⁻¹ ∈ ⨆ R ∈ DSet Ω (conjSub x W), R := by
    have hgc : conjSub x (⨆ R ∈ DSet Ω W, R) ≤ ⨆ R ∈ DSet Ω (conjSub x W), R := by
      simp only [conjSub, Subgroup.map_iSup]
      refine iSup₂_le fun R hR => ?_
      exact le_iSup₂_of_le (f := fun R (_ : R ∈ DSet Ω (conjSub x W)) => R) (conjSub x R)
        (e16g1_dSet_conj h hR x) le_rfl
    exact hgc (conj_mem_conjSub hd.hg)
  have hgt : x * g * x⁻¹ * (x * z * x⁻¹) * (x * g * x⁻¹)⁻¹ =
      x * u * x⁻¹ * (x * e * x⁻¹) := by
    calc x * g * x⁻¹ * (x * z * x⁻¹) * (x * g * x⁻¹)⁻¹ = x * (g * z * g⁻¹) * x⁻¹ := by group
      _ = x * (u * e) * x⁻¹ := by rw [hd.hgt]
      _ = x * u * x⁻¹ * (x * e * x⁻¹) := by group
  refine ⟨c.twin.conj hΩ x, ?_, ?_⟩
  · exact
      { hW := Asc77.WSet.conj hΩ hd.hW x
        hS4 := hS4
        hzW := conj_mem_conjSub hd.hzW
        hu := hu
        huW := conj_mem_conjSub hd.huW
        hu2 := hu2
        hu1 := hu1
        huz := huz
        he := he
        he1 := he1
        he2 := he2
        hg := hg
        hgt := hgt }
  · intro hmem
    rw [← e16g1_conjSub_sup, mem_conjSub_iff] at hmem
    apply c.e_not_mem
    have h1 : x⁻¹ * (x * e * x⁻¹) * x = e := by group
    rwa [h1] at hmem

theorem exists_conj_of_frame {K₂ K₂' W₂ : Subgroup G} {z₂ u₂ e₂ g₂ : G}
    (c : Sit16 Ω K K' W z u e g) (c₂ : Sit16 Ω K₂ K₂' W₂ z₂ u₂ e₂ g₂) (h : EndHyp Ω) :
    ∃ y : G, conjSub y W = W₂ ∧ e₂ = y * e * y⁻¹ := by
  obtain ⟨y, hy⟩ := wSet_conj h c.data.hW c₂.data.hW
  refine ⟨y, hy, ?_⟩
  have hc := (conjG c h y).data.he
  rw [hy] at hc
  have hmem : y * e * y⁻¹ ∈ Subgroup.closure ({e₂} : Set G) := by
    rw [c₂.data.he, ← hc]
    exact Subgroup.subset_closure (Set.mem_singleton _)
  exact (e16g1_eq_of_mem_closure c₂.data.he2 (conjG c h y).data.he1 hmem).symm

theorem exists_frame_of_dSet (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    {W' : Subgroup G} (hW' : W' ∈ WSet Ω) (hKW' : K ∈ DSet Ω W') :
    ∃ u' e' g' : G, Sit16 Ω K K' W' z u' e' g' ∧ ∃ y : G, e' = y * e * y⁻¹ := by
  obtain ⟨x, hx⟩ := wSet_conj h c.data.hW hW'
  have c₁ : Sit16 Ω (conjSub x K) (conjSub x K') W' (x * z * x⁻¹) (x * u * x⁻¹)
      (x * e * x⁻¹) (x * g * x⁻¹) := by
    rw [← hx]
    exact conjG c h x
  have hΩ := h.thmD.hyp.conjInvariant
  have hz₁ : IsUniqueInvolution (conjSub x K) (x * z * x⁻¹) := c₁.twin.isInv
  have hperp : KPerp Ω (conjSub x K) = {conjSub x K, conjSub x K'} :=
    (h.kPerp_eq_twinSet_of_perp9 h9 c₁.twin.mem).trans c₁.twin.twin
  have htrans : ∀ J ∈ Ω, ∃ g₀ : G, conjSub g₀ (conjSub x K) = J := by
    intro J hJ
    obtain ⟨g₀, hg₀⟩ := h.thmD.trans K c.twin.mem J hJ
    exact ⟨g₀ * x⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub, hg₀]⟩
  have hK'₁ : conjSub x K' ∈ twinSet Ω (conjSub x K) := by
    rw [c₁.twin.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨n, hn, hnz⟩ := L94.exists_mGrp_conj ⟨h.thmD.hyp, h.cls, h.thmD.aEmpty⟩ h.thmD.two hW'
    c₁.twin.mem htrans hz₁ hK'₁ c₁.twin.ne.symm hperp c₁.data.hS4
    (h.mem_dSet_of_mem hW' c₁.twin.mem hz₁ c₁.data.hzW) c.twin.mem hKW' c.twin.isInv
  have c₂ := Sit16.conj c₁ h hn
  rw [hnz] at c₂
  have hz₂ : IsUniqueInvolution (conjSub n (conjSub x K)) z := by
    rw [← hnz]
    exact hz₁.conj n
  have hK₂ : conjSub n (conjSub x K) ∈ twinSet Ω K :=
    ⟨hΩ n _ (hΩ x K c.twin.mem), z, c.twin.isInv, hz₂⟩
  rw [c.twin.twin] at hK₂
  rcases hK₂ with hK₂ | hK₂
  ·
    rw [hK₂] at c₂
    have hmem : conjSub n (conjSub x K') ∈ twinSet Ω K := by
      rw [c₂.twin.twin]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [c.twin.twin] at hmem
    rcases hmem with h1 | h1
    · exact absurd h1.symm c₂.twin.ne
    · rw [Set.mem_singleton_iff.mp h1] at c₂
      exact ⟨_, _, _, c₂, x, rfl⟩
  ·
    rw [Set.mem_singleton_iff.mp hK₂] at c₂
    have hmem : conjSub n (conjSub x K') ∈ twinSet Ω K := by
      have h1 : conjSub n (conjSub x K') ∈ twinSet Ω K' := by
        rw [c₂.twin.twin]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      rw [e16g1_twinSet_congr c.twin.mem_twin.2 c.twin.isInv] at h1
      exact h1
    rw [c.twin.twin] at hmem
    rcases hmem with h1 | h1
    · have c₃ := Sit16.symm c₂ h
      rw [h1] at c₃
      exact ⟨_, _, _, c₃, x, rfl⟩
    · exact absurd (Set.mem_singleton_iff.mp h1) c₂.twin.ne.symm

theorem exists_frame_of_omegaStarNbr (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω)
    (h9 : Perp9 Ω) {J' : Subgroup G} (hJ' : J' ∈ omegaStarNbr Ω K) :
    ∃ (W' : Subgroup G) (u' e' g' : G), Sit16 Ω K K' W' z u' e' g' ∧ J' ∈ DSet Ω W' ∧
      ∃ y : G, e' = y * e * y⁻¹ := by
  obtain ⟨W', hW', -, hKW', hJW'⟩ :=
    h.exists_wSet_of_mem_omegaStarNbr c.twin.mem hJ' c.twin.isInv
  obtain ⟨u', e', g', hc, y, hy⟩ := exists_frame_of_dSet c h h9 hW' hKW'
  exact ⟨W', u', e', g', hc, hJW', y, hy⟩

end Sit16

section Vec

variable {Δ P : Set (Subgroup G)} {n : ℕ}

private theorem e16g1_zpowers_mem {P : Set (Subgroup G)} {d : G}
    (hd : ∀ L ∈ P, conjSub d L ∈ P)
    (hdz : ∀ L ∈ P, ∀ r : G, IsUniqueInvolution L r → d * r = r * d) :
    ∀ x ∈ Subgroup.zpowers d, (∀ L ∈ P, conjSub x L ∈ P) ∧
      ∀ L ∈ P, ∀ r : G, IsUniqueInvolution L r → x * r = r * x := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hpos : (0 : ℤ) < (orderOf d : ℤ) := by exact_mod_cast orderOf_pos d
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d ^ k = d ^ m :=
    ⟨(k % (orderOf d : ℤ)).toNat, by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'), zpow_mod_orderOf]⟩
  rw [hm]
  clear hm hx
  induction m with
  | zero =>
    refine ⟨fun L hL => ?_, fun L _ r _ => ?_⟩
    · rw [pow_zero, conjSub_one]
      exact hL
    · rw [pow_zero, one_mul, mul_one]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun L hL => ?_, fun L hL r hr => ?_⟩
    · rw [pow_succ', conjSub_mul]
      exact hd _ (ih1 L hL)
    · rw [pow_succ']
      calc d * d ^ m * r = d * (d ^ m * r) := mul_assoc _ _ _
        _ = d * (r * d ^ m) := by rw [ih2 L hL r hr]
        _ = (d * r) * d ^ m := (mul_assoc _ _ _).symm
        _ = (r * d) * d ^ m := by rw [hdz L hL r hr]
        _ = r * (d * d ^ m) := by rw [mul_assoc]

private theorem e16g1_ofVec_add (u v : Fin n → ZMod 2) :
    AE.Wr.ofVec (u + v) = AE.Wr.ofVec u * AE.Wr.ofVec v := by
  refine AE.Wr.ext ?_ ?_
  · funext i
    simp only [AE.Wr.ofVec, AE.Wr.mul_vec, Pi.add_apply]
    rfl
  · simp [AE.Wr.ofVec, AE.Wr.mul_perm]

theorem exists_vec_of_aeIdent (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {d : G} (hd : ∀ L ∈ P, conjSub d L ∈ P)
    (hdz : ∀ L ∈ P, ∀ r : G, IsUniqueInvolution L r → d * r = r * d) :
    ∃ v : Fin n → ZMod 2, ∀ L ∈ P, ∀ (α : Finset (Fin n)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b →
        (conjSub d L = L ↔ ∑ i ∈ α, v i = 0) ∧
          ((∀ l ∈ L, d * l = l * d) ↔ ∀ i ∈ α, ∀ j ∈ α, v i = v j) := by
  obtain ⟨f, hf, -⟩ := exists_vecHom_of_aeIdent hΩ h2 hPΔ hinv hn5 hn7 I hk (Subgroup.zpowers d)
    (fun x hx => e16g1_zpowers_mem hd hdz x hx)
  obtain ⟨v, -, hv⟩ := hf ⟨d, Subgroup.mem_zpowers d⟩
  exact ⟨v, hv⟩

theorem natCard_le_of_aeIdent (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {A : Subgroup G}
    (hA : ∀ d ∈ A, (∀ L ∈ P, conjSub d L ∈ P) ∧
      ∀ L ∈ P, ∀ r : G, IsUniqueInvolution L r → d * r = r * d)
    {L : Subgroup G} (hL : L ∈ P) (hAL : ∀ a ∈ A, ∀ l ∈ L, a * l = l * a) :
    Nat.card A ≤
      2 ^ (n - 4) * Nat.card ↥(A ⊓ Subgroup.centralizer ((pSpan P : Subgroup G) : Set G)) := by
  classical
  obtain ⟨f, hf, hfix⟩ := exists_vecHom_of_aeIdent hΩ h2 hPΔ hinv hn5 hn7 I hk A hA
  obtain ⟨α₀, h₀, b₀, hlab₀⟩ := I.label L hL
  have hker : Nat.card f.ker ≤
      Nat.card ↥(A ⊓ Subgroup.centralizer ((pSpan P : Subgroup G) : Set G)) := by
    have hmem : ∀ x : f.ker,
        ((x.1 : A) : G) ∈ A ⊓ Subgroup.centralizer ((pSpan P : Subgroup G) : Set G) := by
      intro x
      refine Subgroup.mem_inf.mpr ⟨(x.1 : A).2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact ((hfix x.1).mp (MonoidHom.mem_ker.mp x.2) h hh).symm
    refine Nat.card_le_card_of_injective
      (fun x => (⟨((x.1 : A) : G), hmem x⟩ :
        ↥(A ⊓ Subgroup.centralizer ((pSpan P : Subgroup G) : Set G)))) ?_
    intro x y hxy
    have h1 : ((x.1 : A) : G) = ((y.1 : A) : G) := by
      have := congrArg Subtype.val hxy
      simpa using this
    exact Subtype.ext (Subtype.ext h1)
  set S : Finset (Fin n → ZMod 2) :=
    Finset.univ.filter (fun w => ∀ i ∈ α₀, ∀ j ∈ α₀, w i = w j) with hS
  set R : Finset (AE.AEQ n) := S.image (fun w => AE.mkQ n (AE.Wr.ofVec w)) with hR
  have hSc : S.card = 2 ^ (n - 3) := by
    have := AE.card_vec_const (by omega : 4 ≤ n) α₀ h₀
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    rw [hS]
    exact this
  have hones : AE.mkQ n (AE.Wr.ofVec (fun _ => (1 : ZMod 2))) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (AE.mem_piSub.mpr (Or.inr rfl))
  have hRS : 2 * R.card ≤ S.card := by
    refine Finset.mul_card_image_le_card_of_maps_to (f := fun w => AE.mkQ n (AE.Wr.ofVec w))
      (fun w hw => Finset.mem_image_of_mem (fun w' => AE.mkQ n (AE.Wr.ofVec w')) hw) 2 ?_
    intro b hb
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.mp hb
    have hw0S := (Finset.mem_filter.mp hw0).2
    set w1 : Fin n → ZMod 2 := w0 + fun _ => 1 with hw1
    have hw1S : w1 ∈ S := by
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun i hi j hj => ?_⟩
      simp only [hw1, Pi.add_apply]
      rw [hw0S i hi j hj]
    have hw1f : AE.mkQ n (AE.Wr.ofVec w1) = AE.mkQ n (AE.Wr.ofVec w0) := by
      rw [hw1, e16g1_ofVec_add, map_mul, hones, mul_one]
    have hne : w0 ≠ w1 := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp [hw1] at this
    have hsub : ({w0, w1} : Finset (Fin n → ZMod 2)) ⊆
        S.filter (fun w => AE.mkQ n (AE.Wr.ofVec w) = AE.mkQ n (AE.Wr.ofVec w0)) := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hw0, rfl⟩
      · exact Finset.mem_filter.mpr ⟨hw1S, hw1f⟩
    have h2le := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at h2le
    exact h2le
  have hR2 : R.card ≤ 2 ^ (n - 4) := by
    have h3 : 2 ^ (n - 3) = 2 * 2 ^ (n - 4) := by
      rw [show n - 3 = (n - 4) + 1 by omega, pow_succ]
      ring
    omega
  have hsubR : (f.range : Set (AE.AEQ n)) ⊆ (R : Set (AE.AEQ n)) := by
    rintro g ⟨a, rfl⟩
    obtain ⟨v, hva, hvprop⟩ := hf a
    have hvS : v ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        (hvprop L hL α₀ h₀ b₀ hlab₀).2.mp (fun l hl => hAL (a : G) a.2 l hl)⟩
    show f a ∈ R
    rw [hva, hR]
    exact Finset.mem_image.mpr ⟨v, hvS, rfl⟩
  have hcard_range : Nat.card f.range ≤ R.card := by
    have h4 := Set.ncard_le_ncard hsubR (Finset.finite_toSet R)
    rw [Set.ncard_coe_finset] at h4
    rw [← Nat.card_coe_set_eq] at h4
    exact h4
  have hcardA := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at hcardA
  rw [← hcardA]
  calc Nat.card f.ker * Nat.card f.range ≤
      Nat.card ↥(A ⊓ Subgroup.centralizer ((pSpan P : Subgroup G) : Set G)) * 2 ^ (n - 4) :=
        Nat.mul_le_mul hker (hcard_range.trans hR2)
    _ = 2 ^ (n - 4) * Nat.card ↥(A ⊓ Subgroup.centralizer ((pSpan P : Subgroup G) : Set G)) :=
        Nat.mul_comm _ _

end Vec

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

private theorem e16g2_inter_card {α β γ : Finset (Fin 6)} (hα : α.card = 4) (hβ : β.card = 4)
    (hγ : γ.card = 4)
    (h : AE.zOf (AE.emb α hα) * AE.zOf (AE.emb β hβ) = AE.zOf (AE.emb γ hγ)) :
    (α ∩ β).card = 2 := by
  have hx : ∀ x : Fin 6, ((if x ∈ α then 1 else 0) + (if x ∈ β then 1 else 0) : ZMod 2) =
      if x ∈ γ then 1 else 0 := by
    intro x
    have := congrArg (fun w : AE.Wr 6 => w.vec x) h
    simp only [AE.Wr.mul_vec, AE.zOf_perm, AE.zOf_vec_apply, AE.range_emb, Finset.mem_coe,
      Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply] at this
    simpa using this
  have hγ' : γ = (α ∪ β) \ (α ∩ β) := by
    ext x
    have := hx x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    by_cases ha : x ∈ α <;> by_cases hb : x ∈ β <;> by_cases hc : x ∈ γ <;>
      simp_all <;> revert this <;> decide
  have hsub : α ∩ β ⊆ α ∪ β := Finset.inter_subset_union
  have h1 := Finset.card_sdiff_of_subset hsub
  have h2 := Finset.card_union_add_card_inter α β
  rw [← hγ', hγ] at h1
  omega

private theorem e16g2_conj_mem_of_pSpan {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {a : G}
    {L : Subgroup G} {x : G} (hL : L ∈ centMembers Ω a) (hx : x ∈ pSpan (centMembers Ω a)) :
    conjSub x L ∈ centMembers Ω a := by
  have hc : x ∈ Subgroup.centralizer ({a} : Set G) :=
    (pSpan_le (fun M hM => hM.2) : pSpan (centMembers Ω a) ≤ _) hx
  have hxa : x * a * x⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have := conjSub_mem_centMembers hΩ (n := x) hL
  rwa [hxa] at this

private theorem e16g2_mtrans (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) {A B : Subgroup G}
    (hA : A ∈ DSet Ω W) (hB : B ∈ DSet Ω W) : ∃ m ∈ MGrp Ω W, conjSub m A = B := by
  have h2 := h.thmD.two
  have hΩ := h.thmD.hyp
  have hAΩ := (h.mem_dSet_iff.mp hA).1
  have hBΩ := (h.mem_dSet_iff.mp hB).1
  have hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J →
      T ≤ R ⊔ W ⊔ OCW W := by
    intro R hR T hT J hJ hRJ hTJ
    have hRc : 8 ≤ Nat.card ↥R := hΩ.eight_le_of_mem_RSet hR.1
    have hTc : 8 ≤ Nat.card ↥T := hΩ.eight_le_of_mem_RSet hT.1
    have hJc : Nat.card ↥J = 8 := h.card_eq_eight hJ
    have hRJ' : R = J := Subgroup.eq_of_le_of_card_ge hRJ (by omega)
    have hTJ' : T = J := Subgroup.eq_of_le_of_card_ge hTJ (by omega)
    rw [hTJ', ← hRJ']
    exact le_sup_of_le_left le_sup_left
  have hA' : ∀ K ∈ Ω, AEmpty Ω K := h.thmD.aEmpty
  let c : Q3CL.Thompson.Ctx Ω W := Q3CL.Thompson.Ctx.mk hΩ hW hkey hA'
  have hex : ∃ r ∈ A, r ∉ W := by
    by_contra hcon
    push Not at hcon
    obtain ⟨P, hP, hPnc⟩ := (hΩ.omega1 A hAΩ).2
    apply hPnc
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact Q3CL.Thompson.Ctx.comm_W c _ (hcon _ (hP.1 a.2)) _ (hcon _ (hP.1 b.2))
  have hexB : ∃ r ∈ B, r ∉ W := by
    by_contra hcon
    push Not at hcon
    obtain ⟨P, hP, hPnc⟩ := (hΩ.omega1 B hBΩ).2
    apply hPnc
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact Q3CL.Thompson.Ctx.comm_W c _ (hcon _ (hP.1 a.2)) _ (hcon _ (hP.1 b.2))
  obtain ⟨r, hrA, hrW⟩ := hex
  obtain ⟨r', hr'B, hr'W⟩ := hexB
  have hsyl : ∀ X : Subgroup G, IsPGroup 2 ↥X → IsSylow2In X X := fun X hX =>
    ⟨le_rfl, hX, fun V' hV' _ hle => le_antisymm hV' hle⟩
  let ρ : Asc77.Thompson.Rep Ω W :=
    Asc77.Thompson.Rep.mk A A r hAΩ hA (hsyl A (h2 A hAΩ)) hrA hrW
  let σ : Asc77.Thompson.Rep Ω W :=
    Asc77.Thompson.Rep.mk B B r' hBΩ hB (hsyl B (h2 B hBΩ)) hr'B hr'W
  obtain ⟨m, hm, hmAB⟩ :=
    Q3CL.Thompson.Ctx.exists_conj_of_rep c h.cls (h.not_dbarConnected hW) ρ σ
  exact ⟨m, hm, hmAB⟩

private theorem e16g2_comm_normalizer (c : Sit16 Ω K K' W z u e g) {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) : x * e = e * x := by
  have he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← c.data.he]
    exact Subgroup.subset_closure rfl
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp he.2
  have hyc := Subgroup.mem_center_iff.mp hy ⟨x, hx⟩
  have h1 : x * (y : G) = (y : G) * x := congrArg Subtype.val hyc
  rw [show (y : G) = e from hye] at h1
  exact h1

private theorem e16g2_psi_mem {P : Set (Subgroup G)} (I : AEIdent P 6)
    (ψ : ↥(pSpan P) ≃* ↥(AE.aeSub 6))
    (hmem : ∀ L ∈ P, ∀ (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b →
      ((L.subgroupOf (pSpan P)).map ψ.toMonoidHom).map (AE.aeSub 6).subtype = AE.memAt α hα b)
    {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
    (hLα : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    {x : G} (hx : x ∈ pSpan P) (hxL : x ∈ L) : (ψ ⟨x, hx⟩ : AE.Wr 6) ∈ AE.memAt α hα b := by
  rw [← hmem L hL α hα b hLα]
  refine Subgroup.mem_map.mpr ⟨ψ ⟨x, hx⟩, Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr hxL

private theorem e16g2_psi_inv {P : Set (Subgroup G)} (I : AEIdent P 6)
    (ψ : ↥(pSpan P) ≃* ↥(AE.aeSub 6))
    (hmem : ∀ L ∈ P, ∀ (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b →
      ((L.subgroupOf (pSpan P)).map ψ.toMonoidHom).map (AE.aeSub 6).subtype = AE.memAt α hα b)
    {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
    (hLα : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    {r : G} (hr : r ∈ pSpan P) (hLr : IsUniqueInvolution L r) :
    (ψ ⟨r, hr⟩ : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
  have hmemS := e16g2_psi_mem I ψ hmem hL hLα hr hLr.mem
  have hsq : (ψ ⟨r, hr⟩ : AE.Wr 6) * (ψ ⟨r, hr⟩ : AE.Wr 6) = 1 := by
    have h1 : ψ ⟨r, hr⟩ * ψ ⟨r, hr⟩ = 1 := by
      rw [← map_mul]
      have h2 : (⟨r, hr⟩ : pSpan P) * ⟨r, hr⟩ = 1 := Subtype.ext (by simp [hLr.sq])
      rw [h2, map_one]
    exact congrArg Subtype.val h1
  rcases AE.eq_of_mem_memAt_mul_self hmemS hsq with h3 | h3
  · exfalso
    have h4 : ψ ⟨r, hr⟩ = 1 := Subtype.ext h3
    have h5 : (⟨r, hr⟩ : pSpan P) = 1 := ψ.injective (by rw [h4, map_one])
    exact hLr.ne_one (congrArg Subtype.val h5)
  · exact h3

private theorem e16g2_mem_centMembers_of_inv (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω)
    (h9 : Perp9 Ω) {L : Subgroup G} (hL : L ∈ Ω) {t' : G}
    (ht' : t' = u * e ∨ t' = z * (u * e)) (hLt : IsUniqueInvolution L t') :
    L ∈ centMembers Ω e := by
  have hR : ∃ R ∈ DSet Ω W, IsUniqueInvolution R t' := by
    rcases ht' with rfl | rfl
    · obtain ⟨hJD, -, -, hJu⟩ := conjSub_mem c h h9
      exact ⟨conjSub g K, hJD, hJu⟩
    · obtain ⟨R, hRD, hR⟩ := exists_dSet_zt c h h9
      exact ⟨R, hRD, hR⟩
  obtain ⟨R, hRD, hRt⟩ := hR
  have hLD : L ∈ DSet Ω W := h.twinSet_subset_dSet c.data.hW hRD ⟨hL, t', hRt, hLt⟩
  exact dSet_subset_centMembers c h hLD

private theorem e16g2_comm_memAt {P : Set (Subgroup G)} (I : AEIdent P 6)
    (ψ : ↥(pSpan P) ≃* ↥(AE.aeSub 6))
    (hmem : ∀ L ∈ P, ∀ (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b →
      ((L.subgroupOf (pSpan P)).map ψ.toMonoidHom).map (AE.aeSub 6).subtype = AE.memAt α hα b)
    {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
    (hLα : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    {x : G} (hx : x ∈ pSpan P) (hcomm : ∀ l ∈ L, x * l = l * x) :
    ∀ y ∈ AE.memAt α hα b, (ψ ⟨x, hx⟩ : AE.Wr 6) * y = y * (ψ ⟨x, hx⟩ : AE.Wr 6) := by
  intro y hy
  rw [← hmem L hL α hα b hLα] at hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  have hl : (a' : G) ∈ L := Subgroup.mem_subgroupOf.mp ha'
  have hc : x * (a' : G) = (a' : G) * x := hcomm _ hl
  have h1 : ψ ⟨x, hx⟩ * ψ a' = ψ a' * ψ ⟨x, hx⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  exact congrArg Subtype.val h1

theorem pSpan_le_centralizer_of_mem_lambdaW
    (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    {d : G} (hd : d ∈ lambdaW Ω W) :
    pSpan (centMembers Ω e) ≤ Subgroup.centralizer ({d} : Set G) := by
  simp only [lambdaW, Subgroup.mem_inf] at hd
  obtain ⟨hdD, hdC⟩ := hd
  have s := c.twin
  have hΩc : ConjInvariant Ω := h.thmD.hyp.conjInvariant
  obtain ⟨I, ψ, hI, -, hmem, ⟨heX, hψe⟩, hψD⟩ := exists_equiv_X c h h9 h13
  have hheD : e ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).2
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem c.data.hW s.mem s.isInv c.data.hzW
  have hKP : K ∈ centMembers Ω e := dSet_subset_centMembers c h hKD
  obtain ⟨hJD, -, -, hJu⟩ := conjSub_mem c h h9
  have hJP : conjSub g K ∈ centMembers Ω e := dSet_subset_centMembers c h hJD
  obtain ⟨Rz, hRzD, hRz⟩ := exists_dSet_zt c h h9
  have hRzP : Rz ∈ centMembers Ω e := dSet_subset_centMembers c h hRzD
  have hzX : z ∈ pSpan (centMembers Ω e) := le_pSpan hKP s.isInv.mem
  have htX : u * e ∈ pSpan (centMembers Ω e) := le_pSpan hJP hJu.mem
  have hztX : z * (u * e) ∈ pSpan (centMembers Ω e) := le_pSpan hRzP hRz.mem
  obtain ⟨αK, hαK, bK, hLK⟩ := I.label K hKP
  obtain ⟨αJ, hαJ, bJ, hLJ⟩ := I.label _ hJP
  obtain ⟨αR, hαR, bR, hLR⟩ := I.label Rz hRzP
  have hinv : ∀ (L : Subgroup G), L ∈ centMembers Ω e → ∀ (α : Finset (Fin 6))
      (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (centMembers Ω e))).map I.φ = AE.memBar α hα b →
      ∀ (r : G) (hr : r ∈ pSpan (centMembers Ω e)), IsUniqueInvolution L r →
      (ψ ⟨r, hr⟩ : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
    intro L hL α hα b hLα r hr hLr
    have hmemS : (ψ ⟨r, hr⟩ : AE.Wr 6) ∈ AE.memAt α hα b := by
      rw [← hmem L hL α hα b hLα]
      refine Subgroup.mem_map.mpr ⟨ψ ⟨r, hr⟩, Subgroup.mem_map.mpr ⟨⟨r, hr⟩, ?_, rfl⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr hLr.mem
    have hsq : (ψ ⟨r, hr⟩ : AE.Wr 6) * (ψ ⟨r, hr⟩ : AE.Wr 6) = 1 := by
      have h1 : ψ ⟨r, hr⟩ * ψ ⟨r, hr⟩ = 1 := by
        rw [← map_mul]
        have h2 : (⟨r, hr⟩ : pSpan (centMembers Ω e)) * ⟨r, hr⟩ = 1 :=
          Subtype.ext (by simp [hLr.sq])
        rw [h2, map_one]
      exact congrArg Subtype.val h1
    rcases AE.eq_of_mem_memAt_mul_self hmemS hsq with h3 | h3
    · exfalso
      have h4 : ψ ⟨r, hr⟩ = 1 := Subtype.ext h3
      have h5 : (⟨r, hr⟩ : pSpan (centMembers Ω e)) = 1 := ψ.injective (by rw [h4, map_one])
      exact hLr.ne_one (congrArg Subtype.val h5)
    · exact h3
  have hzψ := hinv K hKP αK hαK bK hLK z hzX s.isInv
  have htψ := hinv _ hJP αJ hαJ bJ hLJ (u * e) htX hJu
  have hztψ := hinv Rz hRzP αR hαR bR hLR (z * (u * e)) hztX hRz
  have hmul : AE.zOf (AE.emb αK hαK) * AE.zOf (AE.emb αJ hαJ) = AE.zOf (AE.emb αR hαR) := by
    rw [← hzψ, ← htψ, ← hztψ]
    have h6 : ψ ⟨z, hzX⟩ * ψ ⟨u * e, htX⟩ = ψ ⟨z * (u * e), hztX⟩ := by
      rw [← map_mul]
      rfl
    exact congrArg Subtype.val h6
  have hcard : (αK ∩ αJ).card = 2 := e16g2_inter_card hαK hαJ hαR hmul
  have hunion : αK ∪ αJ = Finset.univ := by
    apply Finset.eq_univ_of_card
    have h7 := Finset.card_union_add_card_inter αK αJ
    rw [Fintype.card_fin]
    omega
  have hdisj : Disjoint αKᶜ αJᶜ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hx : x ∈ αK ∪ αJ := by
      rw [hunion]
      exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_compl.mp hx1) hx
    · exact (Finset.mem_compl.mp hx2) hx
  have hcK : αKᶜ.card = 2 := by simp [Finset.card_compl, hαK]
  have hcJ : αJᶜ.card = 2 := by simp [Finset.card_compl, hαJ]
  have hdcent := Subgroup.mem_centralizer_iff.mp hdC
  have hKM : K ≤ MGrp Ω W := le_iSup₂ (f := fun R (_ : R ∈ DSet Ω W) => R) K hKD
  have hJM : conjSub g K ≤ MGrp Ω W :=
    le_iSup₂ (f := fun R (_ : R ∈ DSet Ω W) => R) (conjSub g K) hJD
  have hdP : ∀ L ∈ centMembers Ω e, conjSub d L ∈ centMembers Ω e := by
    intro L hL
    have hde : d * e * d⁻¹ = e := by
      rw [h.zGroup_comm h9 d hdD e hheD, mul_inv_cancel_right]
    have := conjSub_mem_centMembers hΩc (n := d) hL
    rwa [hde] at this
  have hdz : ∀ L ∈ centMembers Ω e, ∀ r : G, IsUniqueInvolution L r → d * r = r * d := by
    intro L hL r hr
    exact h.zGroup_comm h9 d hdD r (Subgroup.subset_closure ⟨L, hL.1, hr⟩)
  obtain ⟨v, hv⟩ := exists_vec_of_aeIdent h.thmD.hyp h.thmD.two (fun L hL => hL.1)
    (fun L hL x hx => e16g2_conj_mem_of_pSpan hΩc hL hx) (by norm_num) (by norm_num) I
    hI.ker_two hdP hdz
  have hvK := ((hv K hKP αK hαK bK hLK).2).mp (fun l hl => (hdcent l (hKM hl)).symm)
  have hvJ := ((hv _ hJP αJ hαJ bJ hLJ).2).mp (fun l hl => (hdcent l (hJM hl)).symm)
  have hconst : v = 0 ∨ v = fun _ => 1 := by
    refine AE.const_eq_of_syntheme (p₁ := αKᶜ) (p₂ := αJᶜ) hcK hcJ hdisj v ?_ ?_
    · rw [compl_compl]
      exact hvK
    · rw [compl_compl]
      exact hvJ
  have hall : ∀ i j : Fin 6, v i = v j := by
    rcases hconst with rfl | rfl <;> intro i j <;> simp
  have hPd : ∀ L ∈ centMembers Ω e, L ≤ Subgroup.centralizer ({d} : Set G) := by
    intro L hL l hl
    obtain ⟨α, hα, b, hLα⟩ := I.label L hL
    have := ((hv L hL α hα b hLα).2).mpr (fun i _ j _ => hall i j) l hl
    exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
  exact pSpan_le hPd

theorem lambdaW_eq_centralizer (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    lambdaW Ω W =
      zGroup Ω ⊓ Subgroup.centralizer ((pSpan (centMembers Ω e) : Subgroup G) : Set G) := by
  have hMle : MGrp Ω W ≤ pSpan (centMembers Ω e) := by
    unfold MGrp
    exact iSup₂_le fun R hR => le_pSpan (dSet_subset_centMembers c h hR)
  ext d
  constructor
  · intro hd
    have hd' := hd
    simp only [lambdaW, Subgroup.mem_inf] at hd' ⊢
    refine ⟨hd'.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (pSpan_le_centralizer_of_mem_lambdaW c h h9 h13 hd hx)
  · intro hd
    simp only [Subgroup.mem_inf] at hd
    simp only [lambdaW, Subgroup.mem_inf]
    refine ⟨hd.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hd ⊢
    intro x hx
    exact hd.2 x (hMle hx)

theorem eq_of_mem_zSet_of_mem_sup (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {d : G} (hd : d ∈ zSet Ω)
    (hdK : d ∈ K ⊔ K') : d = z := by
  obtain ⟨L0, hL0, hdL0⟩ := hd
  have s := c.twin
  have hΩc : ConjInvariant Ω := h.thmD.hyp.conjInvariant
  have hdD : d ∈ zGroup Ω := Subgroup.subset_closure ⟨L0, hL0, hdL0⟩
  obtain ⟨I, ψ, hI, -, hmem, ⟨heX, hψe⟩, hψD⟩ := exists_equiv_X c h h9 h13
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem c.data.hW s.mem s.isInv c.data.hzW
  have hKP : K ∈ centMembers Ω e := dSet_subset_centMembers c h hKD
  have hK'D : K' ∈ DSet Ω W := h.mem_dSet_of_mem c.data.hW s.mem_twin.1 s.mem_twin.2 c.data.hzW
  have hK'P : K' ∈ centMembers Ω e := dSet_subset_centMembers c h hK'D
  have hzX : z ∈ pSpan (centMembers Ω e) := le_pSpan hKP s.isInv.mem
  have hdX : d ∈ pSpan (centMembers Ω e) := sup_le (le_pSpan hKP) (le_pSpan hK'P) hdK
  obtain ⟨αK, hαK, bK, hLK⟩ := I.label K hKP
  obtain ⟨αK', hαK', bK', hLK'⟩ := I.label K' hK'P
  have hαeq : αK = αK' := by
    have h1 := e16g2_psi_inv I ψ hmem hKP hLK hzX s.isInv
    have h2 := e16g2_psi_inv I ψ hmem hK'P hLK' hzX s.mem_twin.2
    have h3 := AE.range_eq_of_zOf_eq (h2.symm.trans h1)
    rw [AE.range_emb, AE.range_emb] at h3
    exact Finset.coe_injective h3.symm
  subst hαeq
  let H : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ pSpan (centMembers Ω e),
        AE.SupportedOn (ψ ⟨x, hx⟩ : AE.Wr 6) (Set.range (AE.emb αK hαK))}
      mul_mem' := by
        rintro a b ⟨ha, hsa⟩ ⟨hb, hsb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hab : (ψ ⟨a * b, mul_mem ha hb⟩ : AE.Wr 6) =
            (ψ ⟨a, ha⟩ : AE.Wr 6) * (ψ ⟨b, hb⟩ : AE.Wr 6) := by
          rw [← Subgroup.coe_mul, ← map_mul]
          rfl
        rw [hab]
        exact hsa.mul hsb
      one_mem' := ⟨one_mem _, by
        have h1 : (ψ ⟨1, one_mem _⟩ : AE.Wr 6) = 1 := by
          rw [show (⟨1, one_mem _⟩ : pSpan (centMembers Ω e)) = 1 from rfl, map_one]
          rfl
        rw [h1]
        exact AE.supportedOn_one _⟩
      inv_mem' := by
        rintro a ⟨ha, hsa⟩
        refine ⟨inv_mem ha, ?_⟩
        have hab : (ψ ⟨a⁻¹, inv_mem ha⟩ : AE.Wr 6) = (ψ ⟨a, ha⟩ : AE.Wr 6)⁻¹ := by
          rw [show (⟨a⁻¹, inv_mem ha⟩ : pSpan (centMembers Ω e)) = (⟨a, ha⟩)⁻¹ from rfl,
            map_inv]
          rfl
        rw [hab]
        exact hsa.inv }
  have hKH : K ≤ H := by
    intro x hx
    have hxX : x ∈ pSpan (centMembers Ω e) := le_pSpan hKP hx
    refine ⟨hxX, ?_⟩
    exact AE.supportedOn_of_mem_memAt
      (e16g2_psi_mem I ψ hmem hKP hLK hxX hx)
  have hK'H : K' ≤ H := by
    intro x hx
    have hxX : x ∈ pSpan (centMembers Ω e) := le_pSpan hK'P hx
    refine ⟨hxX, ?_⟩
    exact AE.supportedOn_of_mem_memAt
      (e16g2_psi_mem I ψ hmem hK'P hLK' hxX hx)
  obtain ⟨-, hdS⟩ : ∃ _ : d ∈ pSpan (centMembers Ω e),
      AE.SupportedOn (ψ ⟨d, hdX⟩ : AE.Wr 6) (Set.range (AE.emb αK hαK)) :=
    sup_le hKH hK'H hdK
  set w : AE.Wr 6 := (ψ ⟨d, hdX⟩ : AE.Wr 6) with hw
  have hwperm : w.perm = 1 := (hψD ⟨d, hdX⟩).mp hdD
  have hwsum : ∑ i, w.vec i = 0 := (AE.mem_aeSub.mp (ψ ⟨d, hdX⟩).2).1
  have hwsq : w * w = 1 := by
    have h1 : ψ ⟨d, hdX⟩ * ψ ⟨d, hdX⟩ = 1 := by
      rw [← map_mul]
      have h2 : (⟨d, hdX⟩ : pSpan (centMembers Ω e)) * ⟨d, hdX⟩ = 1 :=
        Subtype.ext (by simp [hdL0.sq])
      rw [h2, map_one]
    exact congrArg Subtype.val h1
  have hwne : w ≠ 1 := by
    intro h1
    have h2 : ψ ⟨d, hdX⟩ = 1 := Subtype.ext h1
    have h3 : (⟨d, hdX⟩ : pSpan (centMembers Ω e)) = 1 := ψ.injective (by rw [h2, map_one])
    exact hdL0.ne_one (congrArg Subtype.val h3)
  have hwS : ∀ i ∉ Set.range (AE.emb αK hαK), w.vec i = 0 := fun i hi => (hdS i hi).1
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 6), S = Finset.univ.filter (fun i => w.vec i = 1) :=
    ⟨_, rfl⟩
  have hmemS : ∀ i, i ∈ S ↔ w.vec i = 1 := by
    intro i
    rw [hS, Finset.mem_filter]
    simp
  have hZ2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hval : ∀ i, w.vec i = if i ∈ S then 1 else 0 := by
    intro i
    rcases hZ2 (w.vec i) with h0 | h1
    · have hnot : i ∉ S := fun hi => by
        have := (hmemS i).mp hi
        rw [h0] at this
        exact zero_ne_one this
      rw [if_neg hnot, h0]
    · rw [if_pos ((hmemS i).mpr h1), h1]
  have hSsub : S ⊆ αK := by
    intro i hi
    by_contra hiα
    have hi' : i ∉ Set.range (AE.emb αK hαK) := by
      rw [AE.range_emb]
      exact_mod_cast hiα
    have h0 := hwS i hi'
    have h1 := (hmemS i).mp hi
    rw [h0] at h1
    exact zero_ne_one h1
  have hsumS : ∑ i, w.vec i = (S.card : ZMod 2) := by
    simp only [hval, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      mul_one]
  have hev : 2 ∣ S.card := by
    have h1 : ((S.card % 2 : ℕ) : ZMod 2) = 0 := by
      rw [ZMod.natCast_mod, ← hsumS, hwsum]
    rcases Nat.mod_two_eq_zero_or_one S.card with h2 | h2
    · exact Nat.dvd_of_mod_eq_zero h2
    · rw [h2] at h1
      exact absurd h1 (by decide)
  have hSle : S.card ≤ 4 := by
    have := Finset.card_le_card hSsub
    rw [hαK] at this
    exact this
  have hSpos : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hwne
    refine AE.Wr.ext (funext fun i => ?_) hwperm
    rw [hval i, hne]
    rfl
  have hSpos' : 0 < S.card := Finset.card_pos.mpr hSpos
  have hzψ := e16g2_psi_inv I ψ hmem hKP hLK hzX s.isInv
  have hcard : S.card = 2 ∨ S.card = 4 := by omega
  rcases hcard with hc2 | hc4
  ·
    exfalso
    obtain ⟨a, b, hab, hS2⟩ := Finset.card_eq_two.mp hc2
    have hβ : ({a, b} : Finset (Fin 6))ᶜ.card = 4 := by
      rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
    obtain ⟨M, hM, hLM⟩ := I.label_surj _ hβ true
    have hMΩ : M ∈ Ω := hM.1
    obtain ⟨rM, hrM⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hMΩ
    have hrMX : rM ∈ pSpan (centMembers Ω e) := le_pSpan hM hrM.mem
    have hrMψ := e16g2_psi_inv I ψ hmem hM hLM hrMX hrM
    have hedX : e * d ∈ pSpan (centMembers Ω e) := mul_mem heX hdX
    have hedψ : (ψ ⟨e * d, hedX⟩ : AE.Wr 6) = AE.zOf (AE.emb _ hβ) := by
      have hsplit : (ψ ⟨e * d, hedX⟩ : AE.Wr 6) = (ψ ⟨e, heX⟩ : AE.Wr 6) * w := by
        have h1 : ψ ⟨e * d, hedX⟩ = ψ ⟨e, heX⟩ * ψ ⟨d, hdX⟩ := by
          rw [← map_mul]
          rfl
        exact congrArg Subtype.val h1
      rw [hsplit, hψe]
      refine AE.Wr.ext (funext fun i => ?_) ?_
      · rw [AE.Wr.mul_vec, AE.zOf_vec_apply]
        have h1 : (AE.Wr.allOnes 6).perm.symm i = i := rfl
        have h2 : (AE.Wr.allOnes 6).vec i = 1 := rfl
        rw [h1, h2, hval i, hS2]
        simp only [AE.range_emb, Finset.mem_coe, Finset.mem_compl, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hi : i = a ∨ i = b
        · simp [hi]
          decide
        · simp [hi]
      · rw [AE.zOf_perm, AE.Wr.mul_perm, hwperm]
        rfl
    have hr_eq : rM = e * d := by
      have h1 : ψ ⟨rM, hrMX⟩ = ψ ⟨e * d, hedX⟩ := Subtype.ext (hrMψ.trans hedψ.symm)
      exact congrArg Subtype.val (ψ.injective h1)
    have hMC : M ≤ Subgroup.centralizer ({d} : Set G) := by
      intro m hm
      have hmX : m ∈ pSpan (centMembers Ω e) := le_pSpan hM hm
      have hmsupp : AE.SupportedOn (ψ ⟨m, hmX⟩ : AE.Wr 6) (Set.range (AE.emb _ hβ)) :=
        AE.supportedOn_of_mem_memAt (e16g2_psi_mem I ψ hmem hM hLM hmX hm)
      have hwS2 : AE.SupportedOn w (((({a, b} : Finset (Fin 6))) : Set (Fin 6))) := by
        intro i hi
        have hi' : i ∉ S := by
          rw [hS2]
          exact fun h' => hi (by exact_mod_cast h')
        refine ⟨?_, ?_⟩
        · rw [hval i, if_neg hi']
        · rw [hwperm]
          rfl
      have hdisj : Disjoint (Set.range (AE.emb _ hβ))
          (((({a, b} : Finset (Fin 6))) : Set (Fin 6))) := by
        rw [AE.range_emb]
        refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
        have hx2' : x ∈ ({a, b} : Finset (Fin 6)) := by exact_mod_cast hx2
        have hx1' : x ∉ ({a, b} : Finset (Fin 6)) := by
          intro hh
          exact (Finset.mem_compl.mp (by exact_mod_cast hx1)) hh
        exact hx1' hx2'
      have hcomm := AE.comm_of_disjoint hmsupp hwS2 hdisj
      have hmd : (⟨m, hmX⟩ : pSpan (centMembers Ω e)) * ⟨d, hdX⟩ =
          ⟨d, hdX⟩ * ⟨m, hmX⟩ := by
        apply ψ.injective
        rw [map_mul, map_mul]
        exact Subtype.ext hcomm
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hmd)
    have hMd : IsUniqueInvolution M d := h.involution_eq_of_le_centralizer h9 hL0 hMΩ hdL0 hMC
    have hdr : d = rM := hMd.eq hrM
    have he_d : e * d = d := hr_eq.symm.trans hdr.symm
    exact c.data.he1 (mul_right_cancel (he_d.trans (one_mul d).symm))
  ·
    have hSeq : S = αK := Finset.eq_of_subset_of_card_le hSsub (by rw [hc4, hαK])
    have hwz : w = AE.zOf (AE.emb αK hαK) := by
      refine AE.Wr.ext (funext fun i => ?_) ?_
      · rw [hval i, AE.zOf_vec_apply]
        simp [AE.range_emb, hSeq]
      · rw [AE.zOf_perm]
        exact hwperm
    have h1 : ψ ⟨d, hdX⟩ = ψ ⟨z, hzX⟩ := Subtype.ext (hwz.trans hzψ.symm)
    exact congrArg Subtype.val (ψ.injective h1)

theorem not_mem_sup_of_omegaStarNbr (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {J' : Subgroup G}
    (hJ' : J' ∈ omegaStarNbr Ω K) (hJ't : J' ∉ twinSet Ω K) {t : G}
    (ht : IsUniqueInvolution J' t) : t ∉ K ⊔ K' := by
  intro htK
  have htz : t ∈ zSet Ω := ⟨J', hJ'.1, ht⟩
  have htz' : t = z := eq_of_mem_zSet_of_mem_sup c h h9 h13 htz htK
  apply hJ't
  refine ⟨hJ'.1, z, c.twin.isInv, ?_⟩
  rw [htz'] at ht
  exact ht

@[expose] def centres (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z : G) : Set G :=
  {e' | ∃ (W' : Subgroup G) (u' g' : G), Sit16 Ω K K' W' z u' e' g'}

theorem eq_of_frames_same_line (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {W₂ : Subgroup G}
    {u₂ e₂ g₂ : G} (c₂ : Sit16 Ω K K' W₂ z u₂ e₂ g₂) {J₁ J₂ : Subgroup G} {r₁ r₂ : G}
    (hJ₁ : J₁ ∈ DSet Ω W) (hJ₂ : J₂ ∈ DSet Ω W₂) (hr₁ : IsUniqueInvolution J₁ r₁)
    (hr₂ : IsUniqueInvolution J₂ r₂) (hr₁z : r₁ ≠ z) (hline : r₂ = r₁ ∨ r₂ = z * r₁) : e₂ = e := by
  have s := c.twin
  have hzsq : z * z = 1 := s.isInv.sq
  have hr₂z : r₂ ≠ z := by
    rcases hline with rfl | rfl
    · exact hr₁z
    · intro hh
      apply hr₁.ne_one
      have h1 : z⁻¹ * (z * r₁) = z⁻¹ * z := by rw [hh]
      simpa using h1
  have hr₁t : r₁ = u * e ∨ r₁ = z * (u * e) := by
    rcases zValues c h h9 J₁ hJ₁ r₁ hr₁ with h1 | h1 | h1
    · exact absurd h1 hr₁z
    · exact Or.inl h1
    · exact Or.inr h1
  have hr₂t : r₂ = u * e ∨ r₂ = z * (u * e) := by
    rcases hline with rfl | rfl
    · exact hr₁t
    · rcases hr₁t with h1 | h1
      · exact Or.inr (by rw [h1])
      · exact Or.inl (by rw [h1, ← mul_assoc, hzsq, one_mul])
  have hr₂u : u₂ * e₂ = u * e ∨ u₂ * e₂ = z * (u * e) := by
    rcases zValues c₂ h h9 J₂ hJ₂ r₂ hr₂ with h1 | h1 | h1
    · exact absurd h1 hr₂z
    · rw [← h1]
      exact hr₂t
    · have h2 : u₂ * e₂ = z * r₂ := by rw [h1, ← mul_assoc, hzsq, one_mul]
      rcases hr₂t with h3 | h3
      · exact Or.inr (by rw [h2, h3])
      · exact Or.inl (by rw [h2, h3, ← mul_assoc, hzsq, one_mul])
  have hKP : K ∈ centMembers Ω e :=
    dSet_subset_centMembers c h (h.mem_dSet_of_mem c.data.hW s.mem s.isInv c.data.hzW)
  have hK'P : K' ∈ centMembers Ω e :=
    dSet_subset_centMembers c h
      (h.mem_dSet_of_mem c.data.hW s.mem_twin.1 s.mem_twin.2 c.data.hzW)
  refine eq_of_dSet_subset_centMembers c c₂ h h9 h13 ?_
  intro R hR
  have hRΩ : R ∈ Ω := (h.mem_dSet_iff.mp hR).1
  obtain ⟨r, hr⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hRΩ
  rcases zValues c₂ h h9 R hR r hr with h1 | h1 | h1
  ·
    have hRz : IsUniqueInvolution R z := h1 ▸ hr
    have hR' : R ∈ twinSet Ω K := ⟨hRΩ, z, s.isInv, hRz⟩
    rw [s.twin] at hR'
    rcases hR' with rfl | rfl
    · exact hKP
    · exact hK'P
  · exact e16g2_mem_centMembers_of_inv c h h9 hRΩ hr₂u (h1 ▸ hr)
  · have hrt : r = u * e ∨ r = z * (u * e) := by
      rcases hr₂u with h2 | h2
      · exact Or.inr (by rw [h1, h2])
      · exact Or.inl (by rw [h1, h2, ← mul_assoc, hzsq, one_mul])
    exact e16g2_mem_centMembers_of_inv c h h9 hRΩ hrt hr

theorem two_le_ncard_centres (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    2 ≤ (centres Ω K K' z).ncard := by
  have heC : e ∈ centres Ω K K' z := ⟨W, u, g, c⟩
  have hΩc : ConjInvariant Ω := h.thmD.hyp.conjInvariant
  have s := c.twin
  have hKP : K ∈ centMembers Ω e :=
    dSet_subset_centMembers c h (h.mem_dSet_of_mem c.data.hW s.mem s.isInv c.data.hzW)
  by_contra hlt
  have hall : ∀ e' ∈ centres Ω K K' z, e' = e := by
    intro e' he'
    by_contra hne
    have hpair : ({e, e'} : Set G) ⊆ centres Ω K K' z := by
      intro x hx
      rcases hx with rfl | rfl
      · exact heC
      · exact he'
    have h2 := Set.ncard_le_ncard hpair (Set.toFinite _)
    rw [Set.ncard_pair (Ne.symm hne)] at h2
    omega
  have hstep : ∀ J' ∈ omegaStarNbr Ω K, J' ∈ centMembers Ω e := by
    intro J' hJ'
    obtain ⟨W', u', e', g', c', hJ'D, -⟩ := exists_frame_of_omegaStarNbr c h h9 hJ'
    have hee : e' = e := hall e' ⟨W', u', g', c'⟩
    have hJ'P := dSet_subset_centMembers c' h hJ'D
    rw [hee] at hJ'P
    exact hJ'P
  have hclosed : ∀ L ∈ centMembers Ω e, ∀ M, dstarAdj Ω L M → M ∈ centMembers Ω e := by
    intro L hL M hLM
    obtain ⟨hM, hLM'⟩ := hLM
    have hML : M ∈ omegaStarNbr Ω L := by
      rcases hLM' with h1 | h1
      · exact h1
      · exact Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hM hL.1 h1
    obtain ⟨x, hx, hxL⟩ := centMembers_oneClass c h h9 K hKP L hL
    have hL' : conjSub x⁻¹ L = K := by
      rw [← hxL, conjSub_inv_conjSub]
    have hconjM : conjSub x⁻¹ M ∈ omegaStarNbr Ω K := by
      have := omegaStarNbr_conj hΩc hML x⁻¹
      rwa [hL'] at this
    have hPM := hstep _ hconjM
    have := e16g2_conj_mem_of_pSpan hΩc hPM hx
    rwa [conjSub_conjSub_inv] at this
  have hreach : ∀ M, Relation.ReflTransGen (dstarAdj Ω) K M → M ∈ centMembers Ω e := by
    intro M hM
    induction hM with
    | refl => exact hKP
    | tail _ hab ih => exact hclosed _ ih _ hab
  have hΩP : ∀ M ∈ Ω, M ∈ centMembers Ω e := fun M hM => hreach M (h.star K s.mem M hM)
  have hXtop : pSpan (centMembers Ω e) = ⊤ := by
    apply top_le_iff.mp
    rw [← h.thmD.gen]
    exact pSpan_le fun M hM => le_pSpan (hΩP M hM)
  have hcen : e ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g'
    have hg' : g' ∈ pSpan (centMembers Ω e) := by
      rw [hXtop]
      exact Subgroup.mem_top g'
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (pSpan_le (fun L hL => hL.2) hg')
  have hbot : e ∈ (⊥ : Subgroup G) := by
    rw [← h.center]
    exact hcen
  exact c.data.he1 (Subgroup.mem_bot.mp hbot)

section E16geAE

open CFSG.ClassicalInvolution.Q3.AE Wr

variable {n : ℕ}


private theorem e16ge_ofVec_mul (u w : Fin n → ZMod 2) : ofVec u * ofVec w = ofVec (u + w) := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rfl
  · simp [ofVec, mul_perm]

private theorem e16ge_ofPerm_conj_ofVec (σ : Equiv.Perm (Fin n)) (w : Fin n → ZMod 2) :
    ofPerm σ * ofVec w * (ofPerm σ)⁻¹ = ofVec (fun x => w (σ.symm x)) := by
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [ofPerm_conj_vec]
    rfl
  · simp [ofPerm, ofVec, inv_perm, mul_perm]

private theorem e16ge_conj_embedVec (ι : Fin 4 ↪ Fin n) {σ : Equiv.Perm (Fin n)}
    {τ : Equiv.Perm (Fin 4)} (hσ : ∀ i, σ (ι i) = ι (τ i)) (v : Fin 4 → ZMod 2) :
    ofPerm σ * ofVec (embedVec ι v) * (ofPerm σ)⁻¹ = ofVec (embedVec ι (v ∘ τ.symm)) := by
  rw [e16ge_ofPerm_conj_ofVec]
  congr 1
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    have h1 : σ.symm (ι i) = ι (τ.symm i) := by
      rw [Equiv.symm_apply_eq, hσ, Equiv.apply_symm_apply]
    rw [h1, embedVec_apply, embedVec_apply]
    rfl
  · have hx' : σ.symm x ∉ Set.range ι := by
      rintro ⟨j, hj⟩
      apply hx
      refine ⟨τ j, ?_⟩
      rw [← hσ, hj, Equiv.apply_symm_apply]
    rw [embedVec_of_not_mem ι _ hx', embedVec_of_not_mem ι _ hx]

private theorem e16ge_zOf_eq (ι : Fin 4 ↪ Fin n) : zOf ι = ofVec (embedVec ι (fun _ => 1)) := by
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [zOf_vec_apply]
    show _ = embedVec ι (fun _ => 1) x
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply, if_pos (Set.mem_range_self i)]
    · rw [if_neg hx, embedVec_of_not_mem ι _ hx]
  · rw [zOf_perm]
    rfl

private theorem e16ge_conj_zOf (ι : Fin 4 ↪ Fin n) {σ : Equiv.Perm (Fin n)}
    {τ : Equiv.Perm (Fin 4)} (hσ : ∀ i, σ (ι i) = ι (τ i)) :
    ofPerm σ * zOf ι * (ofPerm σ)⁻¹ = zOf ι := by
  unfold zOf
  rw [ofPerm_conj_embed hσ, perm_conj_zQ]

private theorem e16ge_perm_extend (ι : Fin 4 ↪ Fin n) (hn : n = 6) (τ : Equiv.Perm (Fin 4)) :
    ∃ σ : Equiv.Perm (Fin n), (∀ i, σ (ι i) = ι (τ i)) ∧ Equiv.Perm.sign σ = 1 := by
  classical
  have h0 : ∀ i, embedPerm ι τ (ι i) = ι (τ i) := fun i => embedPerm_apply ι τ i
  obtain ⟨p, q, hpq, hp, hq⟩ : ∃ p q : Fin n, p ≠ q ∧ p ∉ Set.range ι ∧ q ∉ Set.range ι := by
    have hcard : (Finset.univ.image ι).card = 4 := by
      rw [Finset.card_image_of_injective _ ι.injective]; simp
    have hβ : ((Finset.univ : Finset (Fin n)) \ Finset.univ.image ι).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [hn, hcard]
    obtain ⟨p, q, hpq, hpq'⟩ := Finset.card_eq_two.mp hβ
    have hp : p ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.image ι := by
      rw [hpq']; simp
    have hq : q ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.image ι := by
      rw [hpq']; simp
    refine ⟨p, q, hpq, ?_, ?_⟩
    · rintro ⟨i, hi⟩
      exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    · rintro ⟨i, hi⟩
      exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  rcases Int.units_eq_one_or (Equiv.Perm.sign (embedPerm ι τ)) with hs | hs
  · exact ⟨embedPerm ι τ, h0, hs⟩
  · refine ⟨embedPerm ι τ * Equiv.swap p q, fun i => ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, h0]
      · intro h'; exact hp ⟨i, h'⟩
      · intro h'; exact hq ⟨i, h'⟩
    · rw [Equiv.Perm.sign_mul, hs, Equiv.Perm.sign_swap hpq]
      norm_num



private theorem e16ge_memAt_invol {n : ℕ} (α : Finset (Fin n)) (hα : α.card = 4) (b : Bool)
    {a : Wr n}
    (ha : a ∈ memAt α hα b) (hsq : a * a = 1) (hne : a ≠ 1) : a = zOf (emb α hα) := by
  cases b
  · rcases eq_of_mem_memKStar_mul_self (emb α hα) a ha hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  · rcases eq_of_mem_memK_mul_self (emb α hα) a ha hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1



private theorem e16ge_embedVec_add {n : ℕ} (ι : Fin 4 ↪ Fin n) (u w : Fin 4 → ZMod 2) :
    embedVec ι (u + w) = embedVec ι u + embedVec ι w := by
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [embedVec_apply, Pi.add_apply, Pi.add_apply, embedVec_apply, embedVec_apply]
  · rw [embedVec_of_not_mem ι _ hx, Pi.add_apply, embedVec_of_not_mem ι _ hx,
      embedVec_of_not_mem ι _ hx, add_zero]

private theorem e16ge_embedVec_zero {n : ℕ} (ι : Fin 4 ↪ Fin n) : embedVec ι 0 = 0 := by
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [embedVec_apply]
    rfl
  · rw [embedVec_of_not_mem ι _ hx]
    rfl

private theorem e16ge_embedVec_inj {n : ℕ} (ι : Fin 4 ↪ Fin n) {u w : Fin 4 → ZMod 2}
    (h : embedVec ι u = embedVec ι w) : u = w := by
  funext i
  have := congrFun h (ι i)
  rw [embedVec_apply, embedVec_apply] at this
  exact this

private theorem e16ge_eq_ofVec_embedVec {n : ℕ} (ι : Fin 4 ↪ Fin n) {a : Wr n}
    (ha : SupportedOn a (Set.range ι)) (hp : a.perm = 1) :
    a = ofVec (embedVec ι (fun i => a.vec (ι i))) := by
  refine Wr.ext (funext fun x => ?_) ?_
  · change a.vec x = embedVec ι (fun i => a.vec (ι i)) x
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply]
    · rw [embedVec_of_not_mem ι _ hx]
      exact (ha x hx).1
  · rw [hp]
    rfl

private theorem e16ge_sum_range {n : ℕ} (ι : Fin 4 ↪ Fin n) (w : Fin n → ZMod 2)
    (hw : ∀ x, x ∉ Set.range ι → w x = 0) : (∑ x, w x) = ∑ i, w (ι i) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)) ?_]
  · rw [Finset.sum_image (fun i _ j _ hij => ι.injective hij)]
  · intro x _ hx
    apply hw
    rintro ⟨i, rfl⟩
    exact hx (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private theorem e16ge_E4_cases : ∀ v : Fin 4 → ZMod 2, (∑ i, v i) = 0 →
    v = 0 ∨ v = 1 ∨ v = ![1, 1, 0, 0] ∨ v = ![1, 1, 0, 0] + 1 ∨ v = ![1, 0, 1, 0] ∨
      v = ![1, 0, 1, 0] + 1 ∨ v = ![1, 1, 0, 0] + ![1, 0, 1, 0] ∨
      v = ![1, 1, 0, 0] + ![1, 0, 1, 0] + 1 := by
  decide +kernel



private theorem e16ge_comb : ∀ w₁ w₂ : Fin 4 → ZMod 2,
    ((∑ i, w₁ i) = 0 ∧ (∑ i, w₂ i) = 0 ∧ w₁ ≠ 0 ∧ w₁ ≠ 1 ∧ w₂ ≠ 0 ∧ w₂ ≠ 1 ∧
      w₂ ≠ w₁ ∧ w₂ ≠ w₁ + 1) →
    ∃ τ : Equiv.Perm (Fin 4),
      ((![1, 1, 0, 0] : Fin 4 → ZMod 2) ∘ τ.symm = w₁ ∨
        (![1, 1, 0, 0] : Fin 4 → ZMod 2) ∘ τ.symm = w₁ + 1) ∧
      ((![1, 0, 1, 0] : Fin 4 → ZMod 2) ∘ τ.symm = w₂ ∨
        (![1, 0, 1, 0] : Fin 4 → ZMod 2) ∘ τ.symm = w₂ + 1) := by
  decide +kernel

end E16geAE

private theorem e16ge_comm_of_mem {L : Subgroup G} {z l : G} (hz : IsUniqueInvolution L z)
    (hl : l ∈ L) : z * l = l * z := by
  have h := conj_of_mem_mem hz hl (Or.inr rfl)
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

private theorem e16ge_q8_conj {L : Subgroup G} {z i j : G} (hQ : Q8Data L z i j) :
    i * j * i⁻¹ = z * j ∧ j * i * j⁻¹ = z * i := by
  have hcomm : j * i = z * (i * j) := hQ.comm
  have hzz : z * z = 1 := hQ.inv.sq
  constructor
  · have h1 : i * j = z * (j * i) := by
      rw [hcomm, ← mul_assoc, hzz, one_mul]
    calc i * j * i⁻¹ = z * (j * i) * i⁻¹ := by rw [← h1]
      _ = z * j := by group
  · calc j * i * j⁻¹ = z * (i * j) * j⁻¹ := by rw [hcomm]
      _ = z * i := by group

private theorem e16ge_zpow_involution {z : G} (hzz : z * z = 1) (n : ℤ) :
    z ^ n = 1 ∨ z ^ n = z := by
  have hsq : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hzz]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left
    rw [hm, zpow_mul, hsq, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, hsq, one_zpow, one_mul]

private theorem e16ge_inner_of_mod {L : Subgroup G} {z i j y : G} (hQ : Q8Data L z i j)
    (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hm : ∀ l ∈ L, y * l * y⁻¹ = l ∨ y * l * y⁻¹ = z * l) :
    ∃ w ∈ L, ∀ l ∈ L, y * l * y⁻¹ = w * l * w⁻¹ := by
  have hzi : Commute z i := (e16ge_comm_of_mem hQ.inv hQ.mem_i : z * i = i * z)
  have hzj : Commute z j := (e16ge_comm_of_mem hQ.inv hQ.mem_j : z * j = j * z)
  have hc := e16ge_q8_conj hQ
  have hw : ∃ w ∈ L, w * i * w⁻¹ = y * i * y⁻¹ ∧ w * j * w⁻¹ = y * j * y⁻¹ := by
    have hi' := hm i hQ.mem_i
    have hj' := hm j hQ.mem_j
    rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
    · exact ⟨1, L.one_mem, by rw [hi']; simp, by rw [hj']; simp⟩
    · refine ⟨i, hQ.mem_i, by rw [hi']; group, ?_⟩
      rw [hj', hc.1]
    · refine ⟨j, hQ.mem_j, ?_, by rw [hj']; group⟩
      rw [hi', hc.2]
    · refine ⟨i * j, L.mul_mem hQ.mem_i hQ.mem_j, ?_, ?_⟩
      · rw [hi']
        calc i * j * i * (i * j)⁻¹ = i * (j * i * j⁻¹) * i⁻¹ := by group
          _ = i * (z * i) * i⁻¹ := by rw [hc.2]
          _ = z * i := by
            rw [show i * (z * i) * i⁻¹ = (i * z) * (i * i⁻¹) by group, mul_inv_cancel, mul_one,
              ← hzi.eq]
      · rw [hj']
        calc i * j * j * (i * j)⁻¹ = i * (j * j * j⁻¹) * i⁻¹ := by group
          _ = i * j * i⁻¹ := by group
          _ = z * j := hc.1
  obtain ⟨w, hwL, hwi, hwj⟩ := hw
  set t := w⁻¹ * y with ht
  have hti : Commute t i := by
    show t * i = i * t
    calc t * i = w⁻¹ * (y * i * y⁻¹) * y := by rw [ht]; group
      _ = w⁻¹ * (w * i * w⁻¹) * y := by rw [hwi]
      _ = i * t := by rw [ht]; group
  have htj : Commute t j := by
    show t * j = j * t
    calc t * j = w⁻¹ * (y * j * y⁻¹) * y := by rw [ht]; group
      _ = w⁻¹ * (w * j * w⁻¹) * y := by rw [hwj]
      _ = j * t := by rw [ht]; group
  have htz : Commute t z := by
    have h2 : Commute t (i * i) := hti.mul_right hti
    rw [hQ.sq_i] at h2
    exact h2
  refine ⟨w, hwL, fun l hl => ?_⟩
  have htl : Commute t l := by
    rcases hQ.nf l hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Commute.one_right t
    · exact htz
    · exact hti
    · exact htz.mul_right hti
    · exact htj
    · exact htz.mul_right htj
    · exact hti.mul_right htj
    · exact (htz.mul_right (hti.mul_right htj))
  have htl' : t * l = l * t := htl.eq
  calc y * l * y⁻¹ = w * (t * l) * y⁻¹ := by rw [ht]; group
    _ = w * (l * t) * y⁻¹ := by rw [htl']
    _ = w * l * w⁻¹ := by rw [ht]; group


private theorem e16ge_pair_aux {K K' : Subgroup G} {z k k' k₁ k₁' : G}
    (hzz : z * z = 1) (hzmem : z ∈ K) (hinf : ∀ t ∈ K ⊓ K', t = 1 ∨ t = z)
    (hzK : ∀ l ∈ K, z * l = l * z) (hzK' : ∀ l ∈ K', z * l = l * z)
    (hk : k ∈ K) (hk' : k' ∈ K') (hk1 : k₁ ∈ K) (hk1' : k₁' ∈ K')
    (hrel : k₁' * k₁⁻¹ = k' * k⁻¹ ∨ k₁' * k₁⁻¹ = z * (k' * k⁻¹)) :
    (k₁ = k ∨ k₁ = z * k) ∧ (k₁' = k' ∨ k₁' = z * k') := by
  have hzk' : Commute z k' := hzK' k' hk'
  rcases hrel with hrel | hrel
  ·
    have hk1e : k₁' = k' * k⁻¹ * k₁ := by
      rw [← hrel]; group
    have e1 : k'⁻¹ * k₁' = k⁻¹ * k₁ := by
      rw [hk1e]; group
    have htK : k⁻¹ * k₁ ∈ K := K.mul_mem (K.inv_mem hk) hk1
    have htK' : k⁻¹ * k₁ ∈ K' := by
      rw [← e1]; exact K'.mul_mem (K'.inv_mem hk') hk1'
    have ht := hinf (k⁻¹ * k₁) ⟨htK, htK'⟩
    have hk1x : k₁ = k * (k⁻¹ * k₁) := by group
    have hk1y : k₁' = k' * (k⁻¹ * k₁) := by rw [← e1]; group
    rcases ht with ht | ht
    · rw [ht, mul_one] at hk1x hk1y
      exact ⟨Or.inl hk1x, Or.inl hk1y⟩
    · refine ⟨Or.inr ?_, Or.inr ?_⟩
      · calc k₁ = k * (k⁻¹ * k₁) := hk1x
          _ = k * z := by rw [ht]
          _ = z * k := (hzK k hk).symm
      · calc k₁' = k' * (k⁻¹ * k₁) := hk1y
          _ = k' * z := by rw [ht]
          _ = z * k' := hzk'.eq.symm
  ·
    have hk1e0 : k₁' = z * (k' * k⁻¹) * k₁ := by
      rw [← hrel]; group
    have hk1e : k₁' = z * k' * (k⁻¹ * k₁) := by
      rw [hk1e0]; group
    have hz'k : k'⁻¹ * z = z * k'⁻¹ := hzk'.inv_right.eq.symm
    have e1 : k'⁻¹ * k₁' = z * (k⁻¹ * k₁) := by
      rw [hk1e]
      calc k'⁻¹ * (z * k' * (k⁻¹ * k₁)) = (k'⁻¹ * z) * k' * (k⁻¹ * k₁) := by group
        _ = (z * k'⁻¹) * k' * (k⁻¹ * k₁) := by rw [hz'k]
        _ = z * (k⁻¹ * k₁) := by group
    have htK : k⁻¹ * k₁ ∈ K := K.mul_mem (K.inv_mem hk) hk1
    have htK' : z * (k⁻¹ * k₁) ∈ K' := by
      rw [← e1]; exact K'.mul_mem (K'.inv_mem hk') hk1'
    have htK2 : z * (k⁻¹ * k₁) ∈ K := K.mul_mem hzmem htK
    rcases hinf (z * (k⁻¹ * k₁)) ⟨htK2, htK'⟩ with ht | ht
    · have ht2 : k⁻¹ * k₁ = z := by
        calc k⁻¹ * k₁ = z * (z * (k⁻¹ * k₁)) := by rw [← mul_assoc, hzz, one_mul]
          _ = z := by rw [ht, mul_one]
      have hk1x : k₁ = z * k := by
        calc k₁ = k * (k⁻¹ * k₁) := by group
          _ = k * z := by rw [ht2]
          _ = z * k := (hzK k hk).symm
      have hk1y : k₁' = k' := by
        rw [hk1e, ht2]
        calc z * k' * z = z * (k' * z) := by group
          _ = z * (z * k') := by rw [← hzk'.eq]
          _ = k' := by rw [← mul_assoc, hzz, one_mul]
      exact ⟨Or.inr hk1x, Or.inl hk1y⟩
    · have ht2 : k⁻¹ * k₁ = 1 := by
        calc k⁻¹ * k₁ = z * (z * (k⁻¹ * k₁)) := by rw [← mul_assoc, hzz, one_mul]
          _ = z * z := by rw [ht]
          _ = 1 := hzz
      have hk1x : k₁ = k := by
        calc k₁ = k * (k⁻¹ * k₁) := by group
          _ = k := by rw [ht2, mul_one]
      have hk1y : k₁' = z * k' := by
        rw [hk1e, ht2, mul_one]
      exact ⟨Or.inl hk1x, Or.inr hk1y⟩


private theorem e16ge_qanalysis {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z d₀ : G}
    (h : EndHyp Ω) (s : TwinSit Ω K K' z) (hsw : conjSub d₀ K = K') {y : G}
    (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hm : ∀ k ∈ K, y * (d₀ * k * d₀⁻¹ * k⁻¹) * y⁻¹ = d₀ * k * d₀⁻¹ * k⁻¹ ∨
      y * (d₀ * k * d₀⁻¹ * k⁻¹) * y⁻¹ = z * (d₀ * k * d₀⁻¹ * k⁻¹)) :
    ∃ q ∈ K ⊔ K', ∃ k₀ ∈ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G), y = q * k₀ := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hnf⟩ := exists_q8_gen s.isInv
    (h.isQuatSub_of_mem s.mem) (h.card_eq_eight s.mem)
  obtain ⟨i', j', hi', hj', hii', hjj', hji', hnf'⟩ := exists_q8_gen s.mem_twin.2
    (h.isQuatSub_of_mem s.mem_twin.1) (h.card_eq_eight s.mem_twin.1)
  have hQ : Q8Data K z i j := ⟨s.isInv, hi, hj, hii, hjj, hji, hnf⟩
  have hQ' : Q8Data K' z i' j' := ⟨s.mem_twin.2, hi', hj', hii', hjj', hji', hnf'⟩
  have hyN' : y ∈ Subgroup.normalizer (K' : Set G) := by
    rw [← (h.normalizer_twin s).1]; exact hyN
  have hzz : z * z = 1 := s.isInv.sq
  have hzK : ∀ l ∈ K, z * l = l * z := fun l hl => e16ge_comm_of_mem s.isInv hl
  have hzK' : ∀ l ∈ K', z * l = l * z := fun l hl => e16ge_comm_of_mem s.mem_twin.2 hl
  have hinf : ∀ t ∈ K ⊓ K', t = 1 ∨ t = z := by
    intro t ht
    rw [s.inf_eq_zpowers h] at ht
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact e16ge_zpow_involution hzz n
  have e3 : ∀ a b : G, y * (a * b⁻¹) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹)⁻¹ :=
    fun a b => by group
  have hstep : ∀ k ∈ K, (y * k * y⁻¹ = k ∨ y * k * y⁻¹ = z * k) ∧
      (y * (d₀ * k * d₀⁻¹) * y⁻¹ = d₀ * k * d₀⁻¹ ∨
        y * (d₀ * k * d₀⁻¹) * y⁻¹ = z * (d₀ * k * d₀⁻¹)) := by
    intro k hk
    have hk' : d₀ * k * d₀⁻¹ ∈ K' := by rw [← hsw]; exact conj_mem_conjSub hk
    have hk1 : y * k * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyN k).mp hk
    have hk1' : y * (d₀ * k * d₀⁻¹) * y⁻¹ ∈ K' :=
      (Subgroup.mem_normalizer_iff.mp hyN' _).mp hk'
    have hmk := hm k hk
    rw [e3] at hmk
    exact e16ge_pair_aux hzz s.isInv.mem hinf hzK hzK' hk hk' hk1 hk1' hmk
  have hK : ∀ k ∈ K, y * k * y⁻¹ = k ∨ y * k * y⁻¹ = z * k := fun k hk => (hstep k hk).1
  have hK' : ∀ l ∈ K', y * l * y⁻¹ = l ∨ y * l * y⁻¹ = z * l := by
    intro l hl
    have hl0 : l ∈ conjSub d₀ K := by rw [hsw]; exact hl
    have hk : d₀⁻¹ * l * d₀ ∈ K := mem_conjSub_iff.mp hl0
    have hl' : d₀ * (d₀⁻¹ * l * d₀) * d₀⁻¹ = l := by group
    have := (hstep _ hk).2
    rw [hl'] at this
    exact this
  obtain ⟨w, hw, hwK⟩ := e16ge_inner_of_mod hQ hyN hK
  obtain ⟨w', hw', hwK'⟩ := e16ge_inner_of_mod hQ' hyN' hK'
  set q : G := w * w' with hq
  have hqQ : q ∈ K ⊔ K' :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hw')
  refine ⟨q, hqQ, q⁻¹ * y, ?_, (mul_inv_cancel_left q y).symm⟩
  have hcK : ∀ t ∈ K, y * t * y⁻¹ = q * t * q⁻¹ := by
    intro t ht
    have hcs : w' * t = t * w' := (s.commutes h t ht w' hw').symm
    have h2 : q * t * q⁻¹ = w * t * w⁻¹ := by
      rw [hq, show w * w' * t * (w * w')⁻¹ = w * (w' * t * w'⁻¹) * w⁻¹ by group, hcs]
      group
    rw [hwK t ht, h2]
  have hcK' : ∀ t ∈ K', y * t * y⁻¹ = q * t * q⁻¹ := by
    intro t ht
    have hX : w' * t * w'⁻¹ ∈ K' := K'.mul_mem (K'.mul_mem hw' ht) (K'.inv_mem hw')
    have hcom : w * (w' * t * w'⁻¹) = (w' * t * w'⁻¹) * w := s.commutes h w hw _ hX
    have h2 : q * t * q⁻¹ = w' * t * w'⁻¹ := by
      rw [hq, show w * w' * t * (w * w')⁻¹ = w * (w' * t * w'⁻¹) * w⁻¹ by group, hcom]
      group
    rw [hwK' t ht, h2]
  have hKM : K ≤ Subgroup.centralizer ({q⁻¹ * y} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * (q⁻¹ * y) = q⁻¹ * (q * t * q⁻¹) * y := by group
      _ = q⁻¹ * (y * t * y⁻¹) * y := by rw [← hcK t ht]
      _ = q⁻¹ * y * t := by group
  have hK'M : K' ≤ Subgroup.centralizer ({q⁻¹ * y} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * (q⁻¹ * y) = q⁻¹ * (q * t * q⁻¹) * y := by group
      _ = q⁻¹ * (y * t * y⁻¹) * y := by rw [← hcK' t ht]
      _ = q⁻¹ * y * t := by group
  have hM : K ⊔ K' ≤ Subgroup.centralizer ({q⁻¹ * y} : Set G) := sup_le hKM hK'M
  exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (hM ht)

open scoped Classical in
private noncomputable def e16geΨ (X : Subgroup G) (ψ : ↥X ≃* ↥(AE.aeSub 6))
    (d : G) : AE.Wr 6 :=
  if h : d ∈ X then ((ψ ⟨d, h⟩ : ↥(AE.aeSub 6)) :
    AE.Wr 6) else 1

private theorem e16geΨ_eq {X : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)}
    {d : G} (hd : d ∈ X) :
    e16geΨ X ψ d = ((ψ ⟨d, hd⟩ : ↥(AE.aeSub 6)) :
      AE.Wr 6) := by
  unfold e16geΨ
  rw [dif_pos hd]

private theorem e16geΨ_mul {X : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)}
    {d d' : G} (hd : d ∈ X) (hd' : d' ∈ X) :
    e16geΨ X ψ (d * d') = e16geΨ X ψ d * e16geΨ X ψ d' := by
  rw [e16geΨ_eq hd, e16geΨ_eq hd', e16geΨ_eq (X.mul_mem hd hd')]
  have : (⟨d * d', X.mul_mem hd hd'⟩ : ↥X) = ⟨d, hd⟩ * ⟨d', hd'⟩ := rfl
  rw [this, map_mul]
  rfl


private theorem e16geΨ_inj {X D : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)}
    (hDX : D ≤ X) {d d' : G} (hd : d ∈ D) (hd' : d' ∈ D)
    (h : e16geΨ X ψ d = e16geΨ X ψ d') : d = d' := by
  rw [e16geΨ_eq (hDX hd), e16geΨ_eq (hDX hd')] at h
  have h2 : ψ ⟨d, hDX hd⟩ = ψ ⟨d', hDX hd'⟩ := Subtype.ext h
  exact congrArg Subtype.val (ψ.injective h2)

private theorem e16geΨ_vec_of_mem {X D : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)}
    {ι : Fin 4 ↪ Fin 6} (hDX : D ≤ X)
    (hperm : ∀ d ∈ D, (e16geΨ X ψ d).perm = 1)
    (hsupp : ∀ d ∈ D, AE.SupportedOn (e16geΨ X ψ d) (Set.range ι)) :
    ∀ d ∈ D, ∃ v : Fin 4 → ZMod 2, (∑ i, v i) = 0 ∧
      e16geΨ X ψ d = AE.Wr.ofVec
        (AE.embedVec ι v) := by
  intro d hd
  have hmem : e16geΨ X ψ d ∈ AE.aeSub 6 := by
    rw [e16geΨ_eq (hDX hd)]
    exact (ψ ⟨d, hDX hd⟩).2
  have hsum : (∑ i, (e16geΨ X ψ d).vec i) = 0 := (AE.mem_aeSub.mp hmem).1
  refine ⟨fun i => (e16geΨ X ψ d).vec (ι i), ?_, e16ge_eq_ofVec_embedVec
    ι (hsupp d hd) (hperm d hd)⟩
  rw [← e16ge_sum_range ι _
    (fun x hx => (hsupp d hd x hx).1)]
  exact hsum


private theorem e16geΨ_mul_vec {X D : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)}
    {ι : Fin 4 ↪ Fin 6} (hDX : D ≤ X) {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    {u w : Fin 4 → ZMod 2}
    (hau : e16geΨ X ψ a = AE.Wr.ofVec
      (AE.embedVec ι u))
    (hbw : e16geΨ X ψ b = AE.Wr.ofVec
      (AE.embedVec ι w)) :
    e16geΨ X ψ (a * b) = AE.Wr.ofVec
      (AE.embedVec ι (u + w)) := by
  rw [e16geΨ_mul (hDX ha) (hDX hb), hau, hbw, e16ge_ofVec_mul,
    e16ge_embedVec_add]

private theorem e16geΨ_one {X : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)} :
    e16geΨ X ψ 1 = 1 := by
  rw [e16geΨ_eq X.one_mem]
  have h1 : (⟨1, X.one_mem⟩ : ↥X) = 1 := rfl
  rw [h1, map_one]
  rfl

private theorem e16ge_eight {X D : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)}
    {ι : Fin 4 ↪ Fin 6} (hDX : D ≤ X)
    (hvec : ∀ d ∈ D, ∃ v : Fin 4 → ZMod 2, (∑ i, v i) = 0 ∧
      e16geΨ X ψ d = AE.Wr.ofVec
        (AE.embedVec ι v))
    {z p q : G} (hz : z ∈ D) (hp : p ∈ D) (hq : q ∈ D)
    (hψz : e16geΨ X ψ z = AE.Wr.ofVec
      (AE.embedVec ι (fun _ => 1)))
    (hψp : e16geΨ X ψ p = AE.Wr.ofVec
      (AE.embedVec ι ![1, 1, 0, 0]))
    (hψq : e16geΨ X ψ q = AE.Wr.ofVec
      (AE.embedVec ι ![1, 0, 1, 0])) :
    ∀ d ∈ D, d = 1 ∨ d = z ∨ d = p ∨ d = z * p ∨ d = q ∨ d = z * q ∨ d = p * q ∨
      d = z * (p * q) := by
  intro d hd
  obtain ⟨v, hv, hdv⟩ := hvec d hd
  have hpq : e16geΨ X ψ (p * q) = AE.Wr.ofVec
      (AE.embedVec ι (![1, 1, 0, 0] + ![1, 0, 1, 0])) :=
    e16geΨ_mul_vec hDX hp hq hψp hψq
  have hzpq : e16geΨ X ψ (z * (p * q)) = AE.Wr.ofVec
      (AE.embedVec ι ((fun _ => 1) + (![1, 1, 0, 0] + ![1, 0, 1, 0]))) :=
    e16geΨ_mul_vec hDX hz (D.mul_mem hp hq) hψz hpq
  have hzp : e16geΨ X ψ (z * p) = AE.Wr.ofVec
      (AE.embedVec ι ((fun _ => 1) + ![1, 1, 0, 0])) :=
    e16geΨ_mul_vec hDX hz hp hψz hψp
  have hzq : e16geΨ X ψ (z * q) = AE.Wr.ofVec
      (AE.embedVec ι ((fun _ => 1) + ![1, 0, 1, 0])) :=
    e16geΨ_mul_vec hDX hz hq hψz hψq
  have h1 : e16geΨ X ψ 1 = AE.Wr.ofVec
      (AE.embedVec ι 0) := by
    rw [e16geΨ_one, e16ge_embedVec_zero]
    rfl
  rcases e16ge_E4_cases v hv with rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · left
    exact e16geΨ_inj hDX hd D.one_mem (hdv.trans h1.symm)
  · right; left
    exact e16geΨ_inj hDX hd hz (hdv.trans hψz.symm)
  · right; right; left
    exact e16geΨ_inj hDX hd hp (hdv.trans hψp.symm)
  · right; right; right; left
    refine e16geΨ_inj hDX hd (D.mul_mem hz hp) (hdv.trans ?_)
    rw [hzp, add_comm]
    rfl
  · right; right; right; right; left
    exact e16geΨ_inj hDX hd hq (hdv.trans hψq.symm)
  · right; right; right; right; right; left
    refine e16geΨ_inj hDX hd (D.mul_mem hz hq) (hdv.trans ?_)
    rw [hzq, add_comm]
    rfl
  · right; right; right; right; right; right; left
    exact e16geΨ_inj hDX hd (D.mul_mem hp hq) (hdv.trans hpq.symm)
  · right; right; right; right; right; right; right
    refine e16geΨ_inj hDX hd (D.mul_mem hz (D.mul_mem hp hq)) (hdv.trans ?_)
    rw [hzpq, add_comm]
    rfl

private theorem e16ge_surj {X D : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)}
    {ι : Fin 4 ↪ Fin 6} (hDX : D ≤ X) (hcard : Nat.card ↥D = 8)
    (hvec : ∀ d ∈ D, ∃ v : Fin 4 → ZMod 2, (∑ i, v i) = 0 ∧
      e16geΨ X ψ d = AE.Wr.ofVec
        (AE.embedVec ι v))
    (v : Fin 4 → ZMod 2) (hv : ∑ i, v i = 0) :
    ∃ d ∈ D, e16geΨ X ψ d = AE.Wr.ofVec
      (AE.embedVec ι v) := by
  classical
  let F : G → AE.Wr 6 := fun d => e16geΨ X ψ d
  let f : {w : Fin 4 → ZMod 2 // ∑ i, w i = 0} → AE.Wr 6 :=
    fun w => AE.Wr.ofVec
      (AE.embedVec ι w.1)
  have hf : Function.Injective f := by
    intro w w' h
    apply Subtype.ext
    apply e16ge_embedVec_inj ι
    exact congrArg AE.Wr.vec h
  have hcardT : Nat.card {w : Fin 4 → ZMod 2 // ∑ i, w i = 0} = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hinj : Set.InjOn F (D : Set G) := fun d hd d' hd' h =>
    e16geΨ_inj hDX hd hd' h
  have hDn : (D : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hS : (F '' (D : Set G)).ncard = 8 := by
    rw [hinj.ncard_image, hDn]
  have hTn : (Set.range f).ncard = 8 := by
    rw [Set.ncard_range_of_injective hf, hcardT]
  have hST : F '' (D : Set G) ⊆ Set.range f := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨w, hw, hdw⟩ := hvec d hd
    exact ⟨⟨w, hw⟩, hdw.symm⟩
  have hEq : F '' (D : Set G) = Set.range f :=
    Set.eq_of_subset_of_ncard_le hST (by rw [hS, hTn]) (Set.toFinite _)
  have hmem : f ⟨v, hv⟩ ∈ Set.range f := ⟨⟨v, hv⟩, rfl⟩
  rw [← hEq] at hmem
  obtain ⟨d, hd, hdv⟩ := hmem
  exact ⟨d, hd, hdv⟩

private theorem e16ge_eight_conj {y z p q d : G} (hzz : z * z = 1)
    (hyz : y * z * y⁻¹ = z) (hzp : z * p = p * z) (hzq : z * q = q * z) (hpq : p * q = q * p)
    (h1 : y * p * y⁻¹ = p ∨ y * p * y⁻¹ = z * p) (h2 : y * q * y⁻¹ = q ∨ y * q * y⁻¹ = z * q)
    (hd : d = 1 ∨ d = z ∨ d = p ∨ d = z * p ∨ d = q ∨ d = z * q ∨ d = p * q ∨ d = z * (p * q)) :
    y * d * y⁻¹ = d ∨ y * d * y⁻¹ = z * d := by
  have hmul : ∀ a b : G, y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) :=
    fun a b => by group
  have hzsq : ∀ a : G, z * (z * a) = a := fun a => by rw [← mul_assoc, hzz, one_mul]
  have hpqc : (y * p * y⁻¹) * (y * q * y⁻¹) = p * q ∨
      (y * p * y⁻¹) * (y * q * y⁻¹) = z * (p * q) := by
    have e1 : p * (z * q) = z * (p * q) := by rw [← mul_assoc, ← hzp, mul_assoc]
    have e2 : z * p * (z * q) = p * q := by
      rw [← mul_assoc, mul_assoc z p, ← hzp, ← mul_assoc, hzz, one_mul]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
    · exact Or.inl rfl
    · exact Or.inr e1
    · exact Or.inr (by rw [mul_assoc])
    · exact Or.inl e2
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    simp
  · left
    exact hyz
  · exact h1
  · rw [hmul, hyz]
    rcases h1 with h1 | h1
    · left
      rw [h1]
    · right
      rw [h1, hzsq]
  · exact h2
  · rw [hmul, hyz]
    rcases h2 with h2 | h2
    · left
      rw [h2]
    · right
      rw [h2, hzsq]
  · rw [hmul]
    rcases hpqc with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rw [hmul, hyz, hmul]
    rcases hpqc with h | h
    · rw [h]
      exact Or.inl rfl
    · rw [h, hzsq]
      exact Or.inr rfl

private theorem e16geΨ_inv {X : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)}
    {d : G} (hd : d ∈ X) : e16geΨ X ψ d⁻¹ = (e16geΨ X ψ d)⁻¹ := by
  rw [e16geΨ_eq (X.inv_mem hd), e16geΨ_eq hd]
  have h1 : (⟨d⁻¹, X.inv_mem hd⟩ : ↥X) = (⟨d, hd⟩ : ↥X)⁻¹ := rfl
  rw [h1, map_inv]
  rfl

private theorem e16ge_tau {X D : Subgroup G} {ψ : ↥X ≃* ↥(AE.aeSub 6)}
    {ι : Fin 4 ↪ Fin 6} {e z : G} (hDX : D ≤ X) (hzX : z ∈ X)
    (hz : e16geΨ X ψ z = AE.zOf ι) (heX : e ∈ X)
    (he : e16geΨ X ψ e = AE.Wr.allOnes 6)
    (hperm : ∀ d ∈ D, (e16geΨ X ψ d).perm = 1)
    (hsupp : ∀ d ∈ D, AE.SupportedOn (e16geΨ X ψ d) (Set.range ι))
    (hDn : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (τ : Equiv.Perm (Fin 4)) :
    ∃ c ∈ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      ∀ d ∈ D, c * d * c⁻¹ ∈ D ∧
        ∀ i, (e16geΨ X ψ (c * d * c⁻¹)).vec (ι i) = (e16geΨ X ψ d).vec (ι (τ.symm i)) := by
  obtain ⟨σ, hσ, hsign⟩ := e16ge_perm_extend ι rfl τ
  have hmem : AE.Wr.ofPerm σ ∈ AE.aeSub 6 := by
    rw [AE.mem_aeSub]
    exact ⟨by simp [AE.Wr.wsum, AE.Wr.ofPerm],
      by simpa [AE.Wr.ofPerm] using hsign⟩
  set c₁ : ↥X := ψ.symm ⟨AE.Wr.ofPerm σ, hmem⟩ with hc₁
  set c : G := (c₁ : G) with hc
  have hcX : c ∈ X := c₁.2
  have hψc : e16geΨ X ψ c = AE.Wr.ofPerm σ := by
    rw [e16geΨ_eq hcX]
    have : (⟨c, hcX⟩ : ↥X) = c₁ := rfl
    rw [this, hc₁, MulEquiv.apply_symm_apply]
  have hce : c * e = e * c := by
    have h1 : c₁ * ⟨e, heX⟩ = ⟨e, heX⟩ * c₁ := by
      apply ψ.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      show ((ψ c₁ : ↥(AE.aeSub 6)) : AE.Wr 6) *
        ((ψ ⟨e, heX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) =
        ((ψ ⟨e, heX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) *
        ((ψ c₁ : ↥(AE.aeSub 6)) : AE.Wr 6)
      rw [hc₁, MulEquiv.apply_symm_apply]
      have hE : ((ψ ⟨e, heX⟩ : ↥(AE.aeSub 6)) :
          AE.Wr 6) = AE.Wr.allOnes 6 := by
        rw [← he, e16geΨ_eq heX]
      rw [hE]
      exact (AE.Wr.allOnes_comm _).symm
    exact congrArg Subtype.val h1
  have hcz : c * z = z * c := by
    have h1 : c₁ * ⟨z, hzX⟩ = ⟨z, hzX⟩ * c₁ := by
      apply ψ.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      show ((ψ c₁ : ↥(AE.aeSub 6)) : AE.Wr 6) *
        ((ψ ⟨z, hzX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) =
        ((ψ ⟨z, hzX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) *
        ((ψ c₁ : ↥(AE.aeSub 6)) : AE.Wr 6)
      rw [hc₁, MulEquiv.apply_symm_apply]
      have hZ : ((ψ ⟨z, hzX⟩ : ↥(AE.aeSub 6)) :
          AE.Wr 6) = AE.zOf ι := by
        rw [← hz, e16geΨ_eq hzX]
      rw [hZ]
      have hcomm := e16ge_conj_zOf ι hσ
      exact mul_inv_eq_iff_eq_mul.mp hcomm
    exact congrArg Subtype.val h1
  have hcZ : c ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcz
  refine ⟨c, ⟨Subgroup.mem_centralizer_singleton_iff.mpr hce, hcZ⟩, fun d hd => ?_⟩
  have hdX : d ∈ X := hDX hd
  have hconj : e16geΨ X ψ (c * d * c⁻¹) = AE.Wr.ofPerm σ *
      e16geΨ X ψ d * (AE.Wr.ofPerm σ)⁻¹ := by
    rw [e16geΨ_mul (X.mul_mem hcX hdX) (X.inv_mem hcX), e16geΨ_mul hcX hdX, e16geΨ_inv hcX, hψc]
  refine ⟨hDn c hcZ d hd, fun i => ?_⟩
  have hsymm : σ.symm (ι i) = ι (τ.symm i) := by
    rw [Equiv.symm_apply_eq, hσ, Equiv.apply_symm_apply]
  rw [hconj, AE.ofPerm_conj_vec, hsymm]

private theorem e16ge_mem_sup_decomp {K K' : Subgroup G} (hc : Commutes K K') {x : G}
    (hx : x ∈ K ⊔ K') : ∃ k ∈ K, ∃ k' ∈ K', x = k * k' := by
  let P : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ k' ∈ K', x = k * k'}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, k₁', hk₁', rfl⟩ ⟨k₂, hk₂, k₂', hk₂', rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₁' * k₂', K'.mul_mem hk₁' hk₂', ?_⟩
        have e := hc k₂ hk₂ k₁' hk₁'
        calc k₁ * k₁' * (k₂ * k₂') = k₁ * (k₁' * k₂) * k₂' := by group
          _ = k₁ * (k₂ * k₁') * k₂' := by rw [← e]
          _ = k₁ * k₂ * (k₁' * k₂') := by group
      one_mem' := ⟨1, K.one_mem, 1, K'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, k', hk', rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k'⁻¹, K'.inv_mem hk', ?_⟩
        have e := hc k hk k' hk'
        calc (k * k')⁻¹ = k'⁻¹ * k⁻¹ := by group
          _ = k⁻¹ * k'⁻¹ := by
            have e' : (k' * k)⁻¹ = (k * k')⁻¹ := by rw [e]
            rw [mul_inv_rev, mul_inv_rev] at e'
            exact e'.symm }
  have hle : K ⊔ K' ≤ P := by
    refine sup_le (fun k hk => ⟨k, hk, 1, K'.one_mem, by simp⟩)
      (fun k' hk' => ⟨1, K.one_mem, k', hk', by simp⟩)
  exact hle hx

private theorem e16ge_conj_pair {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G} (h : EndHyp Ω)
    (s : TwinSit Ω K K' z) {x : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub x K = K ∨ conjSub x K = K' := by
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hz' : x * z * x⁻¹ = z := by rw [hxz]; group
  have hinv : IsUniqueInvolution (conjSub x K) z := by
    have := s.isInv.conj x
    rwa [hz'] at this
  have hmem : conjSub x K ∈ twinSet Ω K :=
    ⟨h.thmD.hyp.conjInvariant x K s.mem, z, s.isInv, hinv⟩
  rw [s.twin] at hmem
  rcases Set.mem_insert_iff.mp hmem with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Set.mem_singleton_iff.mp h1)

private theorem e16ge_normQ {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G} (h : EndHyp Ω)
    (s : TwinSit Ω K K' z) {x : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G)) {d : G}
    (hd : d ∈ K ⊔ K') : x * d * x⁻¹ ∈ K ⊔ K' := by
  have hK2 : conjSub x K' = K ∨ conjSub x K' = K' := by
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hz' : x * z * x⁻¹ = z := by rw [hxz]; group
    have hinv : IsUniqueInvolution (conjSub x K') z := by
      have := s.mem_twin.2.conj x
      rwa [hz'] at this
    have hmem : conjSub x K' ∈ twinSet Ω K :=
      ⟨h.thmD.hyp.conjInvariant x K' s.mem_twin.1, z, s.isInv, hinv⟩
    rw [s.twin] at hmem
    rcases Set.mem_insert_iff.mp hmem with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Set.mem_singleton_iff.mp h1)
  have hK1 : conjSub x K ≤ K ⊔ K' := by
    rcases e16ge_conj_pair h s hx with h1 | h1
    · rw [h1]; exact le_sup_left
    · rw [h1]; exact le_sup_right
  have hK2' : conjSub x K' ≤ K ⊔ K' := by
    rcases hK2 with h1 | h1
    · rw [h1]; exact le_sup_left
    · rw [h1]; exact le_sup_right
  have hsup : conjSub x (K ⊔ K') = conjSub x K ⊔ conjSub x K' := Subgroup.map_sup _ _ _
  have hmem := conj_mem_conjSub (n := x) hd
  rw [hsup] at hmem
  exact sup_le hK1 hK2' hmem

private theorem e16ge_model (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ (ι : Fin 4 ↪ Fin 6) (ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)),
      (∀ hzX : z ∈ pSpan (centMembers Ω e),
        ((ψ ⟨z, hzX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) = AE.zOf ι) ∧
      (∀ d ∈ K ⊔ K', ∀ hdX : d ∈ pSpan (centMembers Ω e),
        AE.SupportedOn ((ψ ⟨d, hdX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) (Set.range ι)) ∧
      (∀ d (hdX : d ∈ pSpan (centMembers Ω e)),
        d ∈ zGroup Ω ↔ ((ψ ⟨d, hdX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6).perm = 1) ∧
      (∃ he : e ∈ pSpan (centMembers Ω e),
        ((ψ ⟨e, he⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) = AE.Wr.allOnes 6) := by
  obtain ⟨I, ψ, -, -, hlab, hEe, hD⟩ := exists_equiv_X c h h9 h13
  have hKP : K ∈ centMembers Ω e :=
    c.dSet_subset_centMembers h (h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW)
  have hK'P : K' ∈ centMembers Ω e :=
    c.dSet_subset_centMembers h
      (h.mem_dSet_of_mem c.data.hW c.twin.mem_twin.1 c.twin.mem_twin.2 c.data.hzW)
  obtain ⟨α, hα, b, hKl⟩ := I.label K hKP
  obtain ⟨α', hα', b', hK'l⟩ := I.label K' hK'P
  have hKm : ∀ k ∈ K, ∀ hkX : k ∈ pSpan (centMembers Ω e),
      ((ψ ⟨k, hkX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) ∈ AE.memAt α hα b := by
    intro k hk hkX
    rw [← hlab K hKP α hα b hKl]
    exact Subgroup.mem_map.mpr ⟨ψ ⟨k, hkX⟩, Subgroup.mem_map.mpr
      ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩
  have hK'm : ∀ k ∈ K', ∀ hkX : k ∈ pSpan (centMembers Ω e),
      ((ψ ⟨k, hkX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) ∈ AE.memAt α' hα' b' := by
    intro k hk hkX
    rw [← hlab K' hK'P α' hα' b' hK'l]
    exact Subgroup.mem_map.mpr ⟨ψ ⟨k, hkX⟩, Subgroup.mem_map.mpr
      ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩
  have hzK : z ∈ K := c.twin.isInv.mem
  have hzK' : z ∈ K' := c.twin.mem_twin.2.mem
  have hzX : z ∈ pSpan (centMembers Ω e) := le_pSpan hKP hzK
  have hsq : ((⟨z, hzX⟩ : ↥(pSpan (centMembers Ω e))) * ⟨z, hzX⟩) = 1 :=
    Subtype.ext c.twin.isInv.sq
  have hne : (⟨z, hzX⟩ : ↥(pSpan (centMembers Ω e))) ≠ 1 := by
    intro h1
    apply c.twin.isInv.ne_one
    exact congrArg Subtype.val h1
  have hsq' : ((ψ ⟨z, hzX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) * ((ψ ⟨z, hzX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6)
      = 1 := by
    have h1 := congrArg ψ hsq
    rw [map_mul, map_one] at h1
    exact congrArg Subtype.val h1
  have hne' : ((ψ ⟨z, hzX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) ≠ 1 := by
    intro h1
    apply hne
    apply ψ.injective
    rw [map_one]
    exact Subtype.ext h1
  have hzeq : ((ψ ⟨z, hzX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) = AE.zOf (AE.emb α hα) :=
    e16ge_memAt_invol α hα b (hKm z hzK hzX) hsq' hne'
  have hzX' : z ∈ pSpan (centMembers Ω e) := hzX
  have hzeq' : ((ψ ⟨z, hzX'⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) = AE.zOf (AE.emb α' hα') :=
    e16ge_memAt_invol α' hα' b' (hK'm z hzK' hzX') hsq' hne'
  have hrange : Set.range (AE.emb α' hα') = Set.range (AE.emb α hα) := by
    apply AE.range_eq_of_zOf_eq
    rw [← hzeq', hzeq]
  refine ⟨AE.emb α hα, ψ, fun _ => hzeq, ?_, fun d hd => hD ⟨d, hd⟩, ?_⟩
  · intro d hd hdX
    obtain ⟨k, hk, k', hk', rfl⟩ := e16ge_mem_sup_decomp (TwinSit.commutes c.twin h) hd
    have hkX : k ∈ pSpan (centMembers Ω e) := le_pSpan hKP hk
    have hk'X : k' ∈ pSpan (centMembers Ω e) := le_pSpan hK'P hk'
    have hfac : ((ψ ⟨k * k', hdX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) =
        ((ψ ⟨k, hkX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) * ((ψ ⟨k', hk'X⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) := by
      have hmul : (⟨k * k', hdX⟩ : ↥(pSpan (centMembers Ω e))) = ⟨k, hkX⟩ * ⟨k', hk'X⟩ := rfl
      rw [hmul, map_mul]
      rfl
    rw [hfac]
    refine AE.SupportedOn.mul (AE.supportedOn_of_mem_memAt (hKm k hk hkX)) ?_
    have := AE.supportedOn_of_mem_memAt (hK'm k' hk' hk'X)
    rw [hrange] at this
    exact this
  · exact hEe

private theorem e16ge_realize (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {x : G}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ c₀ ∈ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      ∀ d ∈ zGroup Ω ⊓ (K ⊔ K'),
        c₀⁻¹ * (x * d * x⁻¹) * c₀ = d ∨ c₀⁻¹ * (x * d * x⁻¹) * c₀ = z * d := by
  obtain ⟨ι, ψ, hzψ, hsupp, hDfun, he, hψe⟩ := e16ge_model c h h9 h13
  have hKP : K ∈ centMembers Ω e :=
    c.dSet_subset_centMembers h (h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW)
  have hK'P : K' ∈ centMembers Ω e :=
    c.dSet_subset_centMembers h
      (h.mem_dSet_of_mem c.data.hW c.twin.mem_twin.1 c.twin.mem_twin.2 c.data.hzW)
  have hQX : K ⊔ K' ≤ pSpan (centMembers Ω e) := sup_le (le_pSpan hKP) (le_pSpan hK'P)
  have hDX : zGroup Ω ⊓ (K ⊔ K') ≤ pSpan (centMembers Ω e) := inf_le_right.trans hQX
  have hperm : ∀ d ∈ zGroup Ω ⊓ (K ⊔ K'), (e16geΨ (pSpan (centMembers Ω e)) ψ d).perm = 1 := by
    intro d hd
    rw [e16geΨ_eq (hDX hd)]
    exact (hDfun d (hDX hd)).mp (Subgroup.mem_inf.mp hd).1
  have hsuppD : ∀ d ∈ zGroup Ω ⊓ (K ⊔ K'),
      AE.SupportedOn (e16geΨ (pSpan (centMembers Ω e)) ψ d)
        (Set.range ι) := by
    intro d hd
    rw [e16geΨ_eq (hDX hd)]
    exact hsupp d (Subgroup.mem_inf.mp hd).2 (hDX hd)
  have hvec := e16geΨ_vec_of_mem hDX hperm hsuppD
  have hcard := h.natCard_zGroup_inf_sup_twin h9 c.twin h13
  have hzQ : z ∈ K ⊔ K' := Subgroup.mem_sup_left c.twin.isInv.mem
  have hzD : z ∈ zGroup Ω ⊓ (K ⊔ K') :=
    ⟨Subgroup.subset_closure ⟨K, c.twin.mem, c.twin.isInv⟩, hzQ⟩
  have hzX : z ∈ pSpan (centMembers Ω e) := hQX hzQ
  have hzψ' : e16geΨ (pSpan (centMembers Ω e)) ψ z = AE.zOf ι := by
    rw [e16geΨ_eq hzX]
    exact hzψ hzX
  have hψe' : e16geΨ (pSpan (centMembers Ω e)) ψ e = AE.Wr.allOnes 6 := by
    rw [e16geΨ_eq he]
    exact hψe
  have hzψ'' : e16geΨ (pSpan (centMembers Ω e)) ψ z =
      AE.Wr.ofVec (AE.embedVec ι (fun _ => 1)) :=
    hzψ'.trans (e16ge_zOf_eq ι)
  obtain ⟨p₁, hp₁, hψp₁⟩ := e16ge_surj hDX hcard hvec ![1, 1, 0, 0] (by decide)
  obtain ⟨p₂, hp₂, hψp₂⟩ := e16ge_surj hDX hcard hvec ![1, 0, 1, 0] (by decide)
  have hN := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hcomm : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm h9
  have hzz : z * z = 1 := c.twin.isInv.sq
  have hzp1 : z * p₁ = p₁ * z :=
    hcomm z (Subgroup.mem_inf.mp hzD).1 p₁ (Subgroup.mem_inf.mp hp₁).1
  have hzp2 : z * p₂ = p₂ * z :=
    hcomm z (Subgroup.mem_inf.mp hzD).1 p₂ (Subgroup.mem_inf.mp hp₂).1
  have hp12 : p₁ * p₂ = p₂ * p₁ :=
    hcomm p₁ (Subgroup.mem_inf.mp hp₁).1 p₂ (Subgroup.mem_inf.mp hp₂).1
  have hseven := e16ge_eight hDX hvec hzD hp₁ hp₂ hzψ'' hψp₁ hψp₂
  have hDn : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ d ∈ zGroup Ω ⊓ (K ⊔ K'),
      g * d * g⁻¹ ∈ zGroup Ω ⊓ (K ⊔ K') := fun g hg d hd =>
    ⟨hN.conj_mem _ (Subgroup.mem_inf.mp hd).1 g, e16ge_normQ h c.twin hg (Subgroup.mem_inf.mp hd).2⟩
  let vv : G → Fin 4 → ZMod 2 := fun d i => (e16geΨ (pSpan (centMembers Ω e)) ψ d).vec (ι i)
  have hvv_eq : ∀ d ∈ zGroup Ω ⊓ (K ⊔ K'), ∀ w : Fin 4 → ZMod 2,
      e16geΨ (pSpan (centMembers Ω e)) ψ d = AE.Wr.ofVec
        (AE.embedVec ι w) → vv d = w := by
    intro d _ w hw
    funext i
    show (e16geΨ (pSpan (centMembers Ω e)) ψ d).vec (ι i) = w i
    rw [hw]
    show AE.embedVec ι w (ι i) = w i
    exact AE.embedVec_apply ι w i
  have hvv_inj : ∀ a ∈ zGroup Ω ⊓ (K ⊔ K'), ∀ b ∈ zGroup Ω ⊓ (K ⊔ K'), vv a = vv b → a = b := by
    intro a ha b hb hab
    apply e16geΨ_inj hDX ha hb
    have ea := e16ge_eq_ofVec_embedVec ι (hsuppD a ha) (hperm a ha)
    have eb := e16ge_eq_ofVec_embedVec ι (hsuppD b hb) (hperm b hb)
    exact ea.trans ((congrArg (fun v => AE.Wr.ofVec
      (AE.embedVec ι v)) hab).trans eb.symm)
  have hvv_one : vv 1 = 0 := by
    funext i
    show (e16geΨ (pSpan (centMembers Ω e)) ψ 1).vec (ι i) = 0
    rw [e16geΨ_one]
    rfl
  have hvv_mul : ∀ a ∈ zGroup Ω ⊓ (K ⊔ K'), ∀ b ∈ zGroup Ω ⊓ (K ⊔ K'),
      vv (a * b) = vv a + vv b := by
    intro a ha b hb
    funext i
    show (e16geΨ (pSpan (centMembers Ω e)) ψ (a * b)).vec (ι i) =
      (e16geΨ (pSpan (centMembers Ω e)) ψ a).vec (ι i) +
        (e16geΨ (pSpan (centMembers Ω e)) ψ b).vec (ι i)
    rw [e16geΨ_mul (hDX ha) (hDX hb), AE.Wr.mul_vec, hperm a ha]
    rfl
  have hvv_z : vv z = fun _ => 1 := by
    funext i
    show (e16geΨ (pSpan (centMembers Ω e)) ψ z).vec (ι i) = 1
    rw [hzψ'']
    show AE.embedVec ι (fun _ => 1) (ι i) = 1
    rw [AE.embedVec_apply]
  have hvp1 : vv p₁ = ![1, 1, 0, 0] := hvv_eq p₁ hp₁ _ hψp₁
  have hvp2 : vv p₂ = ![1, 0, 1, 0] := hvv_eq p₂ hp₂ _ hψp₂
  have hvz : vv z = 1 := hvv_z
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hxzc : x * z * x⁻¹ = z := by rw [hxz]; group
  have hconj_inj : ∀ a b : G, x * a * x⁻¹ = x * b * x⁻¹ → a = b := fun a b hab => by
    calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
      _ = x⁻¹ * (x * b * x⁻¹) * x := by rw [hab]
      _ = b := by group
  have hconj_one : ∀ a : G, x * a * x⁻¹ = 1 → a = 1 := fun a ha =>
    hconj_inj a 1 (by rw [ha]; group)
  have hconj_z : ∀ a : G, x * a * x⁻¹ = z → a = z := fun a ha =>
    hconj_inj a z (by rw [ha, hxzc])
  have hconj_mulz : ∀ a b : G, x * a * x⁻¹ = z * (x * b * x⁻¹) → a = z * b := fun a b ha =>
    hconj_inj a (z * b) (by
      rw [ha]
      calc z * (x * b * x⁻¹) = (x * z * x⁻¹) * (x * b * x⁻¹) := by rw [hxzc]
        _ = x * (z * b) * x⁻¹ := by group)
  have hq₁ : x * p₁ * x⁻¹ ∈ zGroup Ω ⊓ (K ⊔ K') := hDn x hx p₁ hp₁
  have hq₂ : x * p₂ * x⁻¹ ∈ zGroup Ω ⊓ (K ⊔ K') := hDn x hx p₂ hp₂
  have hzq₁ : z * (x * p₁ * x⁻¹) ∈ zGroup Ω ⊓ (K ⊔ K') := (zGroup Ω ⊓ (K ⊔ K')).mul_mem hzD hq₁
  obtain ⟨w₁, hw₁s, hw₁⟩ := hvec _ hq₁
  obtain ⟨w₂, hw₂s, hw₂⟩ := hvec _ hq₂
  have hvq₁ : vv (x * p₁ * x⁻¹) = w₁ := hvv_eq _ hq₁ w₁ hw₁
  have hvq₂ : vv (x * p₂ * x⁻¹) = w₂ := hvv_eq _ hq₂ w₂ hw₂
  have hvzq₁ : vv (z * (x * p₁ * x⁻¹)) = w₁ + 1 := by
    rw [hvv_mul z hzD _ hq₁, hvz, hvq₁, add_comm]
  have c1 : w₁ ≠ 0 := by
    intro h0
    have h1 : x * p₁ * x⁻¹ = 1 := hvv_inj _ hq₁ 1 (Subgroup.one_mem _) (by
      rw [hvq₁, h0, hvv_one])
    have hp : p₁ = 1 := hconj_one p₁ h1
    have := hvp1
    rw [hp, hvv_one] at this
    exact absurd this.symm (by decide)
  have c2 : w₁ ≠ 1 := by
    intro h1
    have h2 : x * p₁ * x⁻¹ = z := hvv_inj _ hq₁ z hzD (by rw [hvq₁, h1, hvz])
    have hp : p₁ = z := hconj_z p₁ h2
    have := hvp1
    rw [hp, hvz] at this
    exact absurd this (by decide)
  have c3 : w₂ ≠ 0 := by
    intro h0
    have h1 : x * p₂ * x⁻¹ = 1 := hvv_inj _ hq₂ 1 (Subgroup.one_mem _) (by
      rw [hvq₂, h0, hvv_one])
    have hp : p₂ = 1 := hconj_one p₂ h1
    have := hvp2
    rw [hp, hvv_one] at this
    exact absurd this.symm (by decide)
  have c4 : w₂ ≠ 1 := by
    intro h1
    have h2 : x * p₂ * x⁻¹ = z := hvv_inj _ hq₂ z hzD (by rw [hvq₂, h1, hvz])
    have hp : p₂ = z := hconj_z p₂ h2
    have := hvp2
    rw [hp, hvz] at this
    exact absurd this (by decide)
  have c5 : w₂ ≠ w₁ := by
    intro h1
    have h2 : x * p₂ * x⁻¹ = x * p₁ * x⁻¹ := hvv_inj _ hq₂ _ hq₁ (by rw [hvq₂, hvq₁, h1])
    have hp : p₂ = p₁ := hconj_inj p₂ p₁ h2
    have := hvp2
    rw [hp, hvp1] at this
    exact absurd this (by decide)
  have c6 : w₂ ≠ w₁ + 1 := by
    intro h1
    have h2 : x * p₂ * x⁻¹ = z * (x * p₁ * x⁻¹) := hvv_inj _ hq₂ _ hzq₁
      (by rw [hvq₂, hvzq₁, h1])
    have hp : p₂ = z * p₁ := hconj_mulz p₂ p₁ h2
    have hvp : vv (z * p₁) = 1 + ![1, 1, 0, 0] := by
      rw [hvv_mul z hzD p₁ hp₁, hvz, hvp1]
    have := hvp2
    rw [hp, hvp] at this
    exact absurd this (by decide)
  obtain ⟨τ, hτ1, hτ2⟩ := e16ge_comb w₁ w₂ ⟨hw₁s, hw₂s, c1, c2, c3, c4, c5, c6⟩
  obtain ⟨c₀, hc₀, hcprop⟩ := e16ge_tau hDX hzX hzψ' he hψe' hperm hsuppD hDn τ
  have hvc : ∀ d ∈ zGroup Ω ⊓ (K ⊔ K'), vv (c₀ * d * c₀⁻¹) = vv d ∘ τ.symm := fun d hd =>
    funext fun i => (hcprop d hd).2 i
  have hc0z : c₀ * z = z * c₀ := Subgroup.mem_centralizer_singleton_iff.mp hc₀.2
  have hcz' : c₀⁻¹ * z * c₀ = z := by rw [mul_assoc, ← hc0z, inv_mul_cancel_left]
  have hcp₁ : c₀ * p₁ * c₀⁻¹ = x * p₁ * x⁻¹ ∨ c₀ * p₁ * c₀⁻¹ = z * (x * p₁ * x⁻¹) := by
    have hD1 : c₀ * p₁ * c₀⁻¹ ∈ zGroup Ω ⊓ (K ⊔ K') := (hcprop p₁ hp₁).1
    have hv : vv (c₀ * p₁ * c₀⁻¹) = (![1, 1, 0, 0] : Fin 4 → ZMod 2) ∘ τ.symm := by
      rw [hvc p₁ hp₁, hvp1]
    rcases hτ1 with h1 | h1
    · left
      exact hvv_inj _ hD1 _ hq₁ (by rw [hv, hvq₁, h1])
    · right
      exact hvv_inj _ hD1 _ hzq₁ (by rw [hv, hvzq₁, h1])
  have hcp₂ : c₀ * p₂ * c₀⁻¹ = x * p₂ * x⁻¹ ∨ c₀ * p₂ * c₀⁻¹ = z * (x * p₂ * x⁻¹) := by
    have hD2 : c₀ * p₂ * c₀⁻¹ ∈ zGroup Ω ⊓ (K ⊔ K') := (hcprop p₂ hp₂).1
    have hzq₂ : z * (x * p₂ * x⁻¹) ∈ zGroup Ω ⊓ (K ⊔ K') := (zGroup Ω ⊓ (K ⊔ K')).mul_mem hzD hq₂
    have hv : vv (c₀ * p₂ * c₀⁻¹) = (![1, 0, 1, 0] : Fin 4 → ZMod 2) ∘ τ.symm := by
      rw [hvc p₂ hp₂, hvp2]
    have hvzq₂ : vv (z * (x * p₂ * x⁻¹)) = w₂ + 1 := by
      rw [hvv_mul z hzD _ hq₂, hvz, hvq₂, add_comm]
    rcases hτ2 with h1 | h1
    · left
      exact hvv_inj _ hD2 _ hq₂ (by rw [hv, hvq₂, h1])
    · right
      exact hvv_inj _ hD2 _ hzq₂ (by rw [hv, hvzq₂, h1])
  have hyz : (c₀⁻¹ * x) * z * (c₀⁻¹ * x)⁻¹ = z := by
    calc (c₀⁻¹ * x) * z * (c₀⁻¹ * x)⁻¹ = c₀⁻¹ * (x * z * x⁻¹) * c₀ := by group
      _ = c₀⁻¹ * z * c₀ := by rw [hxzc]
      _ = z := hcz'
  have hy1 : (c₀⁻¹ * x) * p₁ * (c₀⁻¹ * x)⁻¹ = p₁ ∨ (c₀⁻¹ * x) * p₁ * (c₀⁻¹ * x)⁻¹ = z * p₁ := by
    have e : (c₀⁻¹ * x) * p₁ * (c₀⁻¹ * x)⁻¹ = c₀⁻¹ * (x * p₁ * x⁻¹) * c₀ := by group
    rw [e]
    rcases hcp₁ with h | h
    · left
      rw [← h]
      group
    · right
      have hq : x * p₁ * x⁻¹ = z * (c₀ * p₁ * c₀⁻¹) := by
        rw [h, ← mul_assoc, hzz, one_mul]
      rw [hq]
      calc c₀⁻¹ * (z * (c₀ * p₁ * c₀⁻¹)) * c₀ = (c₀⁻¹ * z * c₀) * p₁ := by group
        _ = z * p₁ := by rw [hcz']
  have hy2 : (c₀⁻¹ * x) * p₂ * (c₀⁻¹ * x)⁻¹ = p₂ ∨ (c₀⁻¹ * x) * p₂ * (c₀⁻¹ * x)⁻¹ = z * p₂ := by
    have e : (c₀⁻¹ * x) * p₂ * (c₀⁻¹ * x)⁻¹ = c₀⁻¹ * (x * p₂ * x⁻¹) * c₀ := by group
    rw [e]
    rcases hcp₂ with h | h
    · left
      rw [← h]
      group
    · right
      have hq : x * p₂ * x⁻¹ = z * (c₀ * p₂ * c₀⁻¹) := by
        rw [h, ← mul_assoc, hzz, one_mul]
      rw [hq]
      calc c₀⁻¹ * (z * (c₀ * p₂ * c₀⁻¹)) * c₀ = (c₀⁻¹ * z * c₀) * p₂ := by group
        _ = z * p₂ := by rw [hcz']
  refine ⟨c₀, hc₀, fun d hd => ?_⟩
  have key := e16ge_eight_conj hzz hyz hzp1 hzp2 hp12 hy1 hy2 (hseven d hd)
  have e : c₀⁻¹ * (x * d * x⁻¹) * c₀ = (c₀⁻¹ * x) * d * (c₀⁻¹ * x)⁻¹ := by group
  rw [e]
  exact key


private theorem e16ge_decomp (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {x : G}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ a ∈ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      ∃ k ∈ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G), x = a * k := by
  obtain ⟨c₀, hc₀, hprop⟩ := e16ge_realize c h h9 h13 hx
  have hKe := (c.e_mem_centralizer h).1
  have hK'e := (c.e_mem_centralizer h).2
  have hA_K : K ≤ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
    fun k hk => Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hKe k hk),
      Subgroup.mem_centralizer_singleton_iff.mpr (e16ge_comm_of_mem c.twin.isInv hk).symm⟩
  have hA_K' : K' ≤ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
    fun k hk => Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hK'e k hk),
      Subgroup.mem_centralizer_singleton_iff.mpr
        (e16ge_comm_of_mem c.twin.mem_twin.2 hk).symm⟩
  have hQA : K ⊔ K' ≤ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
    sup_le hA_K hA_K'
  have heD : e ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).2
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, c.twin.mem, c.twin.isInv⟩
  have hDA : zGroup Ω ≤ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
    fun d hd => Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (h.zGroup_comm h9 d hd e heD),
      Subgroup.mem_centralizer_singleton_iff.mpr (h.zGroup_comm h9 d hd z hzD)⟩
  set A : Subgroup G := Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)
    with hAdef
  have hyC : c₀⁻¹ * x ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₀.2) hx
  have hy : ∀ d ∈ zGroup Ω ⊓ (K ⊔ K'), (c₀⁻¹ * x) * d * (c₀⁻¹ * x)⁻¹ = d ∨
      (c₀⁻¹ * x) * d * (c₀⁻¹ * x)⁻¹ = z * d := by
    intro d hd
    have e : (c₀⁻¹ * x) * d * (c₀⁻¹ * x)⁻¹ = c₀⁻¹ * (x * d * x⁻¹) * c₀ := by group
    rw [e]
    exact hprop d hd
  obtain ⟨d₀, hd₀, hsw⟩ := h.exists_mem_zGroup_swap h9 c.twin h13
  have hd₀A : d₀ ∈ A := hDA hd₀
  have hcomm_d : ∀ b ∈ zGroup Ω, d₀⁻¹ * b * d₀ = b := fun b hb => by
    have e := h.zGroup_comm h9 d₀ hd₀ b hb
    calc d₀⁻¹ * b * d₀ = d₀⁻¹ * (b * d₀) := by group
      _ = d₀⁻¹ * (d₀ * b) := by rw [← e]
      _ = b := by group
  have hcomm_dz : d₀⁻¹ * z * d₀ = z := hcomm_d z hzD
  rcases e16ge_conj_pair h c.twin hyC with hK | hK'
  ·
    have hyN : (c₀⁻¹ * x) ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr hK
    have hm : ∀ k ∈ K, (c₀⁻¹ * x) * (d₀ * k * d₀⁻¹ * k⁻¹) * (c₀⁻¹ * x)⁻¹ =
        d₀ * k * d₀⁻¹ * k⁻¹ ∨
        (c₀⁻¹ * x) * (d₀ * k * d₀⁻¹ * k⁻¹) * (c₀⁻¹ * x)⁻¹ =
          z * (d₀ * k * d₀⁻¹ * k⁻¹) := fun k hk =>
      hy _ (Subgroup.mem_inf.mpr (h.commutator_mem_sup_twin h9 c.twin hd₀ hk))
    obtain ⟨q, hq, k₀, hk₀, hyq⟩ := e16ge_qanalysis h c.twin hsw hyN hm
    refine ⟨c₀ * q, A.mul_mem hc₀ (hQA hq), k₀, hk₀, ?_⟩
    calc x = c₀ * (c₀⁻¹ * x) := by group
      _ = c₀ * (q * k₀) := by rw [hyq]
      _ = c₀ * q * k₀ := by group
  ·
    have hsw' : conjSub (d₀⁻¹ * (c₀⁻¹ * x)) K = K := by
      rw [conjSub_mul, hK', ← hsw, conjSub_inv_conjSub]
    have hyN : (d₀⁻¹ * (c₀⁻¹ * x)) ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr hsw'
    have hm : ∀ k ∈ K, (d₀⁻¹ * (c₀⁻¹ * x)) * (d₀ * k * d₀⁻¹ * k⁻¹) *
        (d₀⁻¹ * (c₀⁻¹ * x))⁻¹ = d₀ * k * d₀⁻¹ * k⁻¹ ∨
        (d₀⁻¹ * (c₀⁻¹ * x)) * (d₀ * k * d₀⁻¹ * k⁻¹) * (d₀⁻¹ * (c₀⁻¹ * x))⁻¹ =
          z * (d₀ * k * d₀⁻¹ * k⁻¹) := by
      intro k hk
      have hb : d₀ * k * d₀⁻¹ * k⁻¹ ∈ zGroup Ω ⊓ (K ⊔ K') :=
        h.commutator_mem_sup_twin h9 c.twin hd₀ hk
      have e : (d₀⁻¹ * (c₀⁻¹ * x)) * (d₀ * k * d₀⁻¹ * k⁻¹) * (d₀⁻¹ * (c₀⁻¹ * x))⁻¹ =
          d₀⁻¹ * ((c₀⁻¹ * x) * (d₀ * k * d₀⁻¹ * k⁻¹) * (c₀⁻¹ * x)⁻¹) * d₀ := by group
      rw [e]
      rcases hy _ hb with h1 | h1
      · left
        rw [h1]
        exact hcomm_d _ (Subgroup.mem_inf.mp hb).1
      · right
        rw [h1]
        calc d₀⁻¹ * (z * (d₀ * k * d₀⁻¹ * k⁻¹)) * d₀
            = (d₀⁻¹ * z * d₀) * (d₀⁻¹ * (d₀ * k * d₀⁻¹ * k⁻¹) * d₀) := by group
          _ = z * (d₀ * k * d₀⁻¹ * k⁻¹) := by
            rw [hcomm_dz, hcomm_d _ (Subgroup.mem_inf.mp hb).1]
    obtain ⟨q, hq, k₀, hk₀, hyq⟩ := e16ge_qanalysis h c.twin hsw hyN hm
    refine ⟨c₀ * d₀ * q, A.mul_mem (A.mul_mem hc₀ hd₀A) (hQA hq), k₀, hk₀, ?_⟩
    have hy2 : c₀⁻¹ * x = d₀ * (q * k₀) := by
      calc c₀⁻¹ * x = d₀ * (d₀⁻¹ * (c₀⁻¹ * x)) := by group
        _ = d₀ * (q * k₀) := by rw [hyq]
    calc x = c₀ * (c₀⁻¹ * x) := by group
      _ = c₀ * (d₀ * (q * k₀)) := by rw [hy2]
      _ = c₀ * d₀ * q * k₀ := by group

theorem mem_centralizer_z_decomp (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {x : G}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ k ∈ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G),
      ∃ c' ∈ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        x = k * c' := by
  have hx' : x⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hx
  obtain ⟨a, ha, k₀, hk₀, hxa⟩ := e16ge_decomp c h h9 h13 hx'
  refine ⟨k₀⁻¹, Subgroup.inv_mem _ hk₀, a⁻¹, Subgroup.inv_mem _ ha, ?_⟩
  calc x = (x⁻¹)⁻¹ := (inv_inv x).symm
    _ = (a * k₀)⁻¹ := by rw [hxa]
    _ = k₀⁻¹ * a⁻¹ := mul_inv_rev a k₀

theorem centralizer_sup_le_centralizer_u (c : Sit16 Ω K K' W z u e g) :
    Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Subgroup.mem_centralizer_iff] at hx
  exact (hx u c.data.hu).symm

theorem exists_mem_normalizer_conj_centre (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω)
    (h9 : Perp9 Ω) {e' : G} (he' : e' ∈ centres Ω K K' z) :
    ∃ n ∈ Subgroup.normalizer (K : Set G), n * e * n⁻¹ = e' := by
  obtain ⟨W', u', g', c'⟩ := he'
  have s := c.twin
  have hΩc : ConjInvariant Ω := h.thmD.hyp.conjInvariant
  obtain ⟨x, hx⟩ := wSet_conj h c.data.hW c'.data.hW
  have hKD' : K ∈ DSet Ω W' := h.mem_dSet_of_mem c'.data.hW s.mem s.isInv c'.data.hzW
  have hzx : x * z * x⁻¹ ∈ W' := by
    rw [← hx, mem_conjSub_iff]
    have hid : x⁻¹ * (x * z * x⁻¹) * x = z := by group
    rw [hid]
    exact c.data.hzW
  have hKxD' : conjSub x K ∈ DSet Ω W' :=
    h.mem_dSet_of_mem c'.data.hW (hΩc x K s.mem) (s.isInv.conj x) hzx
  obtain ⟨m, hm, hmK⟩ := e16g2_mtrans h c'.data.hW hKD' hKxD'
  have hMle : MGrp Ω W' ≤ Subgroup.normalizer (W' : Set G) := by
    unfold MGrp
    exact iSup₂_le fun R hR => (h.mem_dSet_iff.mp hR).2
  have hmN : m ∈ Subgroup.normalizer (W' : Set G) := hMle hm
  set n : G := m⁻¹ * x with hn
  have hnK : conjSub n K = K := by
    rw [hn, conjSub_mul, ← hmK, conjSub_inv_conjSub]
  have hnW : conjSub n W = W' := by
    rw [hn, conjSub_mul, hx]
    exact mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ hmN)
  have heW : e ∈ W := by
    have he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
      rw [← c.data.he]
      exact Subgroup.subset_closure rfl
    exact he.1
  have hnorm : ∀ w ∈ Subgroup.normalizer (W' : Set G),
      n⁻¹ * w * n ∈ Subgroup.normalizer (W : Set G) := by
    intro w hw
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    have hwW := mem_normalizer_iff_conjSub_eq.mp hw
    rw [conjSub_mul, conjSub_mul, hnW, hwW, ← hnW, conjSub_inv_conjSub]
  set y : G := n * e * n⁻¹ with hy
  have hyN : y ∈ Subgroup.normalizer (W' : Set G) := by
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    have hinv : conjSub n⁻¹ W' = W := by
      rw [← hnW, conjSub_inv_conjSub]
    have heN : conjSub e W = W := mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer heW)
    rw [hy, conjSub_mul, conjSub_mul, hinv, heN, hnW]
  have hyW : y ∈ W' := by
    rw [← hnW, hy, mem_conjSub_iff]
    have hid : n⁻¹ * (n * e * n⁻¹) * n = e := by group
    rw [hid]
    exact heW
  have hyc : y ∈ Asc77.centerIn (Subgroup.normalizer (W' : Set G)) := by
    refine Subgroup.mem_map.mpr ⟨⟨y, hyN⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro w
    obtain ⟨w, hw⟩ := w
    have hc : (n⁻¹ * w * n) * e = e * (n⁻¹ * w * n) :=
      e16g2_comm_normalizer c (hnorm w hw)
    apply Subtype.ext
    show (w : G) * y = y * (w : G)
    rw [hy]
    calc (w : G) * (n * e * n⁻¹) = n * ((n⁻¹ * w * n) * e) * n⁻¹ := by group
      _ = n * (e * (n⁻¹ * w * n)) * n⁻¹ := by rw [hc]
      _ = n * e * n⁻¹ * w := by group
  have hyE : y ∈ W' ⊓ Asc77.centerIn (Subgroup.normalizer (W' : Set G)) := ⟨hyW, hyc⟩
  rw [← c'.data.he, Subgroup.mem_closure_singleton] at hyE
  obtain ⟨k, hk⟩ := hyE
  have hsq : e' ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact c'.data.he2
  have hk2 : e' ^ k = e' ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, hsq, one_zpow, mul_one]
  have hy1 : y ≠ 1 := by
    intro h1
    apply c.data.he1
    have h2 : e = n⁻¹ * y * n := by
      rw [hy]
      group
    rw [h2, h1, mul_one, inv_mul_cancel]
  refine ⟨n, mem_normalizer_iff_conjSub_eq.mpr hnK, ?_⟩
  show y = e'
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · exfalso
    apply hy1
    rw [← hk, hk2, h0, zpow_zero]
  · rw [← hk, hk2, h0, zpow_one]

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13

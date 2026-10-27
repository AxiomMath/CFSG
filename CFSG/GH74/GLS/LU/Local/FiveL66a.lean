module

public import CFSG.GH74.GLS.LU.Local.ActBridge
public import CFSG.GH74.GLS.LU.Local.FiveL83a
public import CFSG.GH74.GLS.LU.Local.FiveCfg2
public import CFSG.GH74.GLS.LU.Local.Torus1

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section L66a

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

theorem FiveCtx.toLUCtx (c : FiveCtx G p f z S K₁ K₂ t u) : LUCtx G p f z S K₁ K₂ t u 1 :=
  ⟨c.simple, c.prime, c.odd, le_of_eq c.pf.symm, c.hyp, c.eps⟩

theorem FiveCtx.hc (c : FiveCtx G p f z S K₁ K₂ t u) : LUComps G (p ^ f) z K₁ K₂ := c.hyp.1

theorem FiveCtx.hs (c : FiveCtx G p f z S K₁ K₂ t u) : LUSyl G z S K₁ K₂ t u := c.hyp.2.1

theorem FiveCtx.card_A0 (c : FiveCtx G p f z S K₁ K₂ t u) : Nat.card ↥(A0 z) = 1 := by
  have hodd : Odd (Nat.card ↥(A0 z)) := odd_card_pPrimeCoreOf (Cz z)
  have hd := c.eps.A0_dvd
  rw [c.pf] at hd
  have h4 : Nat.card ↥(A0 z) ∣ 4 := by
    have : ((Nat.card ↥(A0 z) : ℕ) : ℤ) ∣ ((4 : ℕ) : ℤ) := by
      have e : ((5 : ℕ) : ℤ) - 1 = ((4 : ℕ) : ℤ) := by norm_num
      rwa [e] at hd
    exact Int.natCast_dvd_natCast.mp this
  have hle : Nat.card ↥(A0 z) ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  have hpos : 0 < Nat.card ↥(A0 z) := Nat.card_pos
  obtain ⟨m, hm⟩ := hodd
  interval_cases hc : Nat.card ↥(A0 z)
  · rfl
  · omega
  · exact absurd h4 (by norm_num)
  · omega

theorem FiveCtx.A0_eq_bot (c : FiveCtx G p f z S K₁ K₂ t u) : A0 z = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ c.card_A0

theorem centralizes_of_centralizes_sylow {K R : Subgroup G} {z : G} {r : ℕ}
    (hmod : HasSL2Model ↥K (fun s => s = 5)) (hcen : (center ↥K).map K.subtype = zpowers z)
    (hz2 : z * z = 1) (hr : r.Prime) (hr2 : r ≠ 2) (hRK : R ≤ K)
    (hR : Nat.card ↥R = 2 ^ (Nat.card ↥K).factorization 2)
    {y : G} (hy : y ∈ normalizer (K : Set G)) (hyr : y ^ r = 1) (hyR : ∀ x ∈ R, y * x = x * y) :
    ∀ k ∈ K, y * k = k * y := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hF : Nat.card (ZMod 5) = 5 ^ 1 := by simp
  obtain ⟨e⟩ := exists_mulEquiv_SL2 hmod (ZMod 5) (by simp)
  have hγr : actAut e y hy ^ r = 1 := by
    have h1 := actAut_pow e hy r
    have h2 : actAut e (y ^ r) ((normalizer (K : Set G)).pow_mem hy r) = 1 := by
      have : actAut e (y ^ r) ((normalizer (K : Set G)).pow_mem hy r) =
          actAut e 1 ((normalizer (K : Set G)).one_mem) := actAut_congr e _ _ hyr
      rw [this]; exact actAut_one e
    rw [← h1]; exact h2
  obtain ⟨y₀, hy₀r, hy₀⟩ := exists_odd_lift (F := ZMod 5) (p := 5) (f := 1) (r := r) Nat.prime_five hF
    (by norm_num) (by norm_num) hr hr2 (by
      intro h
      exact hr.one_lt.ne' (Nat.dvd_one.mp h)) hγr
  set k : G := (e y₀ : G) with hk
  have hkK : k ∈ K := (e y₀).2
  have hkR : ∀ x ∈ R, k * x = x * k := by
    intro x hx
    have hxK : x ∈ K := hRK hx
    set M : SL(2, ZMod 5) := e.symm ⟨x, hxK⟩ with hM
    have h1 := coe_actAut e hy M
    have hexM : ((e M : ↥K) : G) = x := by rw [hM]; simp
    rw [hexM, hyR x hx] at h1
    have h2 : actAut e y hy M = y₀ * M * y₀⁻¹ := by
      rw [hy₀]; simp [MulAut.conj_apply]
    rw [h2] at h1
    have h3 : ((e (y₀ * M * y₀⁻¹) : ↥K) : G) = k * x * k⁻¹ := by
      simp [hk, hexM]
    rw [h3] at h1
    have : k * x * k⁻¹ = x := by rw [h1]; group
    calc k * x = (k * x * k⁻¹) * k := by group
      _ = x * k := by rw [this]
  have hkZ := cent_sylow_mem_center SL2.sl2SylowLeaf hmod (by decide) (le_refl 5) hRK hR hkK hkR
  rw [hcen] at hkZ
  have hkr : k ^ r = 1 := by
    have := congrArg (fun a : SL(2, ZMod 5) => ((e a : ↥K) : G)) hy₀r
    simpa [hk] using this
  have hk1 : k = 1 := by
    rcases mem_zpowers_of_sq_eq_one hz2 hkZ with h | h
    · exact h
    · have hodd : Odd r := hr.odd_of_ne_two hr2
      obtain ⟨m, hm⟩ := hodd
      have hz1 : z = 1 := by
        have e1 : z ^ r = z := by
          rw [hm, pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul]
        rw [h] at hkr
        rw [← e1]; exact hkr
      rw [h, hz1]
  have hy₀1 : y₀ = 1 := by
    have : e y₀ = 1 := Subtype.ext hk1
    exact e.injective (by rw [this, map_one])
  have hγ1 : actAut e y hy = 1 := by
    rw [hy₀, hy₀1]; ext M; simp
  exact (actAut_eq_one_iff e hy).mp hγ1

theorem FiveCtx.hc5 (c : FiveCtx G p f z S K₁ K₂ t u) : LUComps G 5 z K₁ K₂ := by
  have := c.hc
  rwa [c.pf] at this

theorem FiveCtx.Fstar_eq_bot (c : FiveCtx G p f z S K₁ K₂ t u) :
    Fstar (S : Subgroup G) K₁ K₂ u = ⊥ := by
  classical
  have : IsCyclic ↥(A0 z) := c.eps.A0_cyc
  have hc := c.hc5
  have hs := c.hs
  have hgs : GenSyl G z S K₁ K₂ t u := hs.toGen
  rw [eq_bot_iff]
  intro y hy
  by_contra hy1
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [h]; exact Subgroup.one_mem _)
  have hyodd : Odd (orderOf y) := odd_orderOf_pPrimeCoreOf hy
  have hord1 : orderOf y ≠ 1 := fun h => hy1' (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hord1
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hyodd) (even_iff_two_dvd.mpr hrd)
  set y' : G := y ^ (orderOf y / r) with hy'
  have hy'ord : orderOf y' = r := orderOf_pow_orderOf_div (orderOf_pos y).ne' hrd
  have hy'F : y' ∈ Fstar (S : Subgroup G) K₁ K₂ u := Subgroup.pow_mem _ hy _
  have hy'C : y' ∈ Cz z := Fstar_le_Cz hc hs hy'F
  have hy'r : y' ^ r = 1 := by rw [← hy'ord]; exact pow_orderOf_eq_one y'
  have hycent : y' ∈ centralizer (((S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊔ zpowers u : Subgroup G) : Set G) :=
    Subgroup.map_subtype_le _ hy'F
  have hy'Q : ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), y' * x = x * y' := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hycent x (Subgroup.mem_sup_left hx)).symm
  have hodd' : Odd (orderOf y') := by rw [hy'ord]; exact hr.odd_of_ne_two hr2
  obtain ⟨hy1m, hy2m⟩ := hc.odd_fix hy'C hodd'
  have hn₁ : y' ∈ normalizer (K₁ : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hy1m
  have hn₂ : y' ∈ normalizer (K₂ : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hy2m
  have hz2 : z * z = 1 := hs.z_sq
  have hQ₁ : ∀ x ∈ (S : Subgroup G) ⊓ K₁, y' * x = x * y' := fun x hx =>
    hy'Q x ⟨hx.1, Subgroup.mem_sup_left hx.2⟩
  have hQ₂ : ∀ x ∈ (S : Subgroup G) ⊓ K₂, y' * x = x * y' := fun x hx =>
    hy'Q x ⟨hx.1, Subgroup.mem_sup_right hx.2⟩
  have h1 := centralizes_of_centralizes_sylow hc.sl₁ hc.cen₁ hz2 hr hr2 inf_le_right
    (card_Q₁ hc hgs) hn₁ hy'r hQ₁
  have h2 := centralizes_of_centralizes_sylow hc.sl₂ hc.cen₂ hz2 hr hr2 inf_le_right
    (card_Q₂ hc hgs) hn₂ hy'r hQ₂
  have hCK : y' ∈ CCK z K₁ K₂ := by
    rw [mem_CCK]
    refine ⟨hy'C, fun k hk => ?_⟩
    have hle : K₁ ⊔ K₂ ≤ centralizer ({y'} : Set G) := by
      refine sup_le (fun k hk => ?_) (fun k hk => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h1 k hk).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h2 k hk).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm
  have hA : y' ∈ A0 z := odd_mem_A0_of_centralizes hs hc hCK hodd'
  rw [c.A0_eq_bot, Subgroup.mem_bot] at hA
  rw [hA, orderOf_one] at hy'ord
  exact hr.one_lt.ne hy'ord

theorem FiveCtx.Cz_eq (c : FiveCtx G p f z S K₁ K₂ t u) : Cz z = (K₁ ⊔ K₂) ⊔ (S : Subgroup G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, k, hk, s, hsS, y, hy, rfl⟩ := c.hyp.2.2.2.2 x hx
    rw [c.A0_eq_bot, Subgroup.mem_bot] at ha
    rw [c.Fstar_eq_bot, Subgroup.mem_bot] at hy
    subst ha; subst hy
    simpa using Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hsS)
  · exact sup_le (K_le_Cz c.hc5) c.hs.S_le_Cz

theorem FiveCtx.card_K (c : FiveCtx G p f z S K₁ K₂ t u) : Nat.card ↥(K₁ ⊔ K₂) = 7200 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsCyclic ↥(A0 z) := c.eps.A0_cyc
  have h := card_K_mul_two c.hc5 c.hs.toGen
  obtain ⟨e₁⟩ := exists_mulEquiv_SL2 c.hc5.sl₁ (ZMod 5) (by simp)
  obtain ⟨e₂⟩ := exists_mulEquiv_SL2 c.hc5.sl₂ (ZMod 5) (by simp)
  rw [sl2_five_card e₁, sl2_five_card e₂] at h
  omega

theorem FiveCtx.card_Cz (c : FiveCtx G p f z S K₁ K₂ t u) : Nat.card ↥(Cz z) = 28800 := by
  have : IsCyclic ↥(A0 z) := c.eps.A0_cyc
  have hS : (S : Subgroup G) ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact c.hc5.conj_sup_mem (c.hs.S_le_Cz hs) hx
    · intro hx
      have h2 := c.hc5.conj_sup_mem ((Cz z).inv_mem (c.hs.S_le_Cz hs)) hx
      have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
      rwa [e] at h2
  have h := card_sup_mul_card_inf' hS
  have hcS := c.hs.card_S
  have hK := c.card_K
  have hpos : 0 < Nat.card ↥((S : Subgroup G) ⊓ (K₁ ⊔ K₂)) := Nat.card_pos
  rw [hcS, hK] at h
  rw [c.Cz_eq, sup_comm]
  have h3 : Nat.card ↥((S : Subgroup G) ⊔ (K₁ ⊔ K₂)) * Nat.card ↥((S : Subgroup G) ⊓ (K₁ ⊔ K₂)) =
      28800 * Nat.card ↥((S : Subgroup G) ⊓ (K₁ ⊔ K₂)) := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos h3

theorem FiveCtx.card_K₁ (c : FiveCtx G p f z S K₁ K₂ t u) : Nat.card ↥K₁ = 120 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := exists_mulEquiv_SL2 c.hc5.sl₁ (ZMod 5) (by simp)
  exact sl2_five_card e

end L66a

end CFSG.GH74.GLS.LU.Local.Five

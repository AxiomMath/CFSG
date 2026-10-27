module

public import CFSG.CGT.PushingUpLit.CGT6.EmbRes
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.YuBasic
public import CFSG.CGT.PushingUpLit.CGT6.EmbX

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section USelf

variable {V : Type} [CommGroup V]

@[expose] def USelf (K : Subgroup (MulAut V)) : Prop :=
  ∀ N : Subgroup V, (∀ g ∈ K, ∀ u ∈ commV K, g u * u⁻¹ ∈ N) → commV K ≤ N

variable {K : Subgroup (MulAut V)}

theorem USelf.le_commVW (h : USelf K) : commV K ≤ commVW (commV K) K :=
  h _ fun _ hg _ hu => mem_commVW hg hu

theorem USelf_of_le_commVW (h : commV K ≤ commVW (commV K) K) : USelf K := fun _ hN =>
  h.trans (commVW_le hN)

theorem USelf_of_perfect (hK : ⁅K, K⁆ = K) : USelf K := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  exact fun N hN => commV_le_of_perfect K N fun g u => hN g g.2 u u.2

theorem USelf_of_odd [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hodd : Odd (Nat.card ↥K)) :
    USelf K := by
  classical
  have hbot : commV K ⊓ fixV K = ⊥ := commV_inf_fixV_eq_bot_of_odd hV K hodd
  intro N hN u hu
  have : Fintype ↥K := Fintype.ofFinite _
  set n : V := ∏ σ : ↥K, (σ : MulAut V) u with hn
  have hn1 : n ∈ commV K := Subgroup.prod_mem _ fun σ _ => apply_mem_commV_self K σ.2 hu
  have hn2 : n ∈ fixV K := by
    intro τ hτ
    have h1 : (τ : MulAut V) n = ∏ σ : ↥K, (τ : MulAut V) ((σ : MulAut V) u) :=
      map_prod (τ : MulAut V).toMonoidHom _ _
    rw [h1]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : ↥K)) _ _ (fun σ => by
      simp [MulAut.mul_apply])
  have hn3 : n = 1 := by
    have : n ∈ commV K ⊓ fixV K := ⟨hn1, hn2⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hprod : n = (∏ σ : ↥K, ((σ : MulAut V) u * u⁻¹)) * u ^ Nat.card ↥K := by
    have h1 : ∀ σ : ↥K, (σ : MulAut V) u = ((σ : MulAut V) u * u⁻¹) * u := fun σ => by group
    calc n = ∏ σ : ↥K, (((σ : MulAut V) u * u⁻¹) * u) := by
          rw [hn]
          exact Finset.prod_congr rfl fun σ _ => h1 σ
      _ = (∏ σ : ↥K, ((σ : MulAut V) u * u⁻¹)) * ∏ _σ : ↥K, u := Finset.prod_mul_distrib
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hpmem : (∏ σ : ↥K, ((σ : MulAut V) u * u⁻¹)) ∈ N :=
    Subgroup.prod_mem _ fun σ _ => hN σ σ.2 u hu
  obtain ⟨m, hm⟩ := hodd
  have hu1 : u ^ Nat.card ↥K = u := by
    rw [hm, pow_succ, pow_mul, hV u, one_pow, one_mul]
  rw [hu1] at hprod
  have : u = (∏ σ : ↥K, ((σ : MulAut V) u * u⁻¹))⁻¹ := by
    rw [hn3] at hprod
    exact (eq_inv_of_mul_eq_one_right hprod.symm)
  rw [this]
  exact N.inv_mem hpmem

end USelf

section Conj

variable {V : Type} [CommGroup V]

theorem conj_mul_apply (g y : MulAut V) (v : V) :
    (g * y * g⁻¹) v * v⁻¹ = g (y (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
  simp [MulAut.mul_apply]

theorem apply_mem_commV_conj (g : MulAut V) {Y : Subgroup (MulAut V)} {w : V}
    (hw : w ∈ commV Y) : g w ∈ commV (Y.map (MulAut.conj g).toMonoidHom) := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨k, hk, v, rfl⟩ := hw
    have h1 : g (k v * v⁻¹) = (g * k * g⁻¹) (g v) * (g v)⁻¹ := by
      simp [MulAut.mul_apply, MulAut.inv_apply]
    rw [h1]
    exact Subgroup.subset_closure ⟨g * k * g⁻¹, ⟨k, hk, by simp [MulAut.conj_apply]⟩, g v, rfl⟩
  | one => simp
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact inv_mem ha

theorem conjClosure_le_trivQ {Y Xt : Subgroup (MulAut V)} {N : Subgroup V}
    (hN : ∀ g ∈ Xt, ∀ y ∈ Y, ∀ v : V, (g * y * g⁻¹ : MulAut V) v * v⁻¹ ∈ N) :
    conjClosure Y Xt ≤ trivQ N := by
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩ v
  exact hN g hg y hy v

theorem USelf_conjClosure {Y : Subgroup (MulAut V)} (Xt : Subgroup (MulAut V)) (h : USelf Y) :
    USelf (conjClosure Y Xt) := by
  apply USelf_of_le_commVW
  rw [commV_le_iff_le_trivQ]
  apply conjClosure_le_trivQ
  intro g hg y hy v
  rw [conj_mul_apply]
  have h1 : y (g⁻¹ v) * (g⁻¹ v)⁻¹ ∈ commVW (commV Y) Y :=
    h.le_commVW (Subgroup.subset_closure ⟨y, hy, g⁻¹ v, rfl⟩)
  have hmap : commVW (commV Y) Y ≤
      (commVW (commV (conjClosure Y Xt)) (conjClosure Y Xt)).comap (g : MulAut V).toMonoidHom := by
    apply commVW_le
    intro k hk w hw
    rw [Subgroup.mem_comap]
    have h2 : (g : MulAut V).toMonoidHom (k w * w⁻¹) = (g * k * g⁻¹) (g w) * (g w)⁻¹ := by
      simp [MulAut.mul_apply, MulAut.inv_apply]
    rw [h2]
    exact mem_commVW (mem_conjClosure_of_mem hg hk)
      (commV_mono (map_conj_le_conjClosure hg) (apply_mem_commV_conj g hw))
  exact hmap h1

end Conj

section Short

variable {V : Type} [CommGroup V] [Finite V] {K : Subgroup (MulAut V)}

omit [Finite V] in
theorem yuInc_mem_shortU_of (hV : ∀ v : V, v ^ 2 = 1) (hK : USelf K) (u : ↥(commV K)) :
    yuInc K u ∈ shortU ↥(yuHol K) := by
  let N₁ : Subgroup V := ((shortU ↥(yuHol K)).comap (yuInc K)).map (commV K).subtype
  have hN : ∀ g ∈ K, ∀ w ∈ commV K, g w * w⁻¹ ∈ N₁ := by
    intro g hg w hw
    refine ⟨⟨g w * w⁻¹, Subgroup.subset_closure ⟨g, hg, w, rfl⟩⟩, ?_, rfl⟩
    have hc := comm_yuInc_yuSec K ⟨g, hg⟩ (⟨w, hw⟩ : ↥(commV K))⁻¹
    have hmem : ⁅yuInc K (⟨w, hw⟩ : ↥(commV K))⁻¹, yuSec K ⟨g, hg⟩⁆ ∈ shortU ↥(yuHol K) :=
      Subgroup.commutator_mem_commutator (yuInc_range_le_pCore K hV ⟨_, rfl⟩)
        (Subgroup.mem_top _)
    rw [hc] at hmem
    have : (⟨((((⟨w, hw⟩ : ↥(commV K))⁻¹ : ↥(commV K))) : V) *
        (g : MulAut V) (((((⟨w, hw⟩ : ↥(commV K))⁻¹ : ↥(commV K))) : V))⁻¹,
        mul_mem (inv_mem hw) (apply_mem_commV_self K hg (inv_mem (inv_mem hw)))⟩ : ↥(commV K)) =
        ⟨g w * w⁻¹, Subgroup.subset_closure ⟨g, hg, w, rfl⟩⟩ := by
      apply Subtype.ext
      show w⁻¹ * g (w⁻¹)⁻¹ = g w * w⁻¹
      rw [inv_inv, mul_comm]
    rw [this] at hmem
    exact hmem
  obtain ⟨u', hu', hu'u⟩ := hK N₁ hN u.2
  have : u' = u := Subtype.ext hu'u
  rw [← this]
  exact hu'

omit [Finite V] in
theorem shortU_yuHol_eq_range (hV : ∀ v : V, v ^ 2 = 1) (hK : USelf K)
    (hOK : ⁅oTwoIn K, K⁆ = ⊥) : shortU ↥(yuHol K) = (yuInc K).range := by
  apply le_antisymm
  · rw [← ker_yuProj]
    exact shortU_yuHol_le_ker hV hOK
  · rintro _ ⟨u, rfl⟩
    exact yuInc_mem_shortU_of hV hK u

omit [Finite V] in
theorem oResidualTwo_yuHol_conjClosure {Y Xt : Subgroup (MulAut V)}
    (hNo : SubTwo.NoTwoQuotient Y) (hY : USelf Y) :
    oResidualTwo ↥(yuHol (conjClosure Y Xt)) = ⊤ := by
  obtain ⟨K, hKdef⟩ : ∃ K, K = conjClosure Y Xt := ⟨_, rfl⟩
  rw [← hKdef, oResidualTwo_eq_top_iff]
  intro N hN hpow
  have hUK : USelf K := hKdef ▸ USelf_conjClosure Xt hY
  have hNn : (N.comap (yuSec K)).Normal := hN.comap _
  let N₁ : Subgroup (MulAut V) := (N.comap (yuSec K)).map K.subtype
  have hNK : K ≤ Subgroup.normalizer (N₁ : Set (MulAut V)) := by
    have h1 : (⊤ : Subgroup ↥K).map K.subtype ≤ Subgroup.normalizer (N₁ : Set (MulAut V)) := by
      have := Subgroup.le_normalizer_map (H := N.comap (yuSec K)) K.subtype
      rwa [Subgroup.normalizer_eq_top (N.comap (yuSec K))] at this
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  have hgen : ∀ g ∈ Xt, ∀ y ∈ Y, g * y * g⁻¹ ∈ N₁ := by
    intro g hg y hy
    have hFX : Y.map (MulAut.conj g).toMonoidHom ≤ K := hKdef ▸ map_conj_le_conjClosure hg
    have hFno : SubTwo.NoTwoQuotient (Y.map (MulAut.conj g).toMonoidHom) :=
      noTwoQuotient_map_hom _ hNo
    have hFle : Y.map (MulAut.conj g).toMonoidHom ≤ N₁ := by
      have h := hFno (N₁ ⊓ Y.map (MulAut.conj g).toMonoidHom) inf_le_right
        (le_trans (le_inf (hFX.trans hNK) Subgroup.le_normalizer)
          Subgroup.inf_normalizer_le_normalizer_inf) (fun f hf => by
          obtain ⟨k, hk⟩ := hpow (yuSec K ⟨f, hFX hf⟩)
          refine ⟨k, ⟨⟨(⟨f, hFX hf⟩ : ↥K) ^ 2 ^ k, ?_, ?_⟩, Subgroup.pow_mem _ hf _⟩⟩
          · show _ ∈ N.comap (yuSec K)
            rw [Subgroup.mem_comap, map_pow]
            exact hk
          · rfl)
      rw [← h]
      exact inf_le_left
    exact hFle ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hsec : ∀ k : ↥K, yuSec K k ∈ N := by
    intro k
    have hKN : K ≤ N₁ := by
      refine hKdef.le.trans ?_
      rw [conjClosure, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, hy, rfl⟩
      exact hgen g hg y hy
    obtain ⟨z, hz, hzk⟩ := hKN k.2
    have : z = k := Subtype.ext hzk
    rw [← this]
    exact hz
  let M₁ : Subgroup V := (N.comap (yuInc K)).map (commV K).subtype
  have hMg : ∀ g ∈ K, ∀ w ∈ commV K, g w * w⁻¹ ∈ M₁ := by
    intro g hg w hw
    refine ⟨⟨g w * w⁻¹, Subgroup.subset_closure ⟨g, hg, w, rfl⟩⟩, ?_, rfl⟩
    have hc := comm_yuInc_yuSec K ⟨g, hg⟩ (⟨w, hw⟩ : ↥(commV K))⁻¹
    have hmem : ⁅yuInc K (⟨w, hw⟩ : ↥(commV K))⁻¹, yuSec K ⟨g, hg⟩⁆ ∈ N := by
      rw [commutatorElement_def]
      exact N.mul_mem (hN.conj_mem _ (hsec ⟨g, hg⟩) _) (N.inv_mem (hsec ⟨g, hg⟩))
    rw [hc] at hmem
    have : (⟨((((⟨w, hw⟩ : ↥(commV K))⁻¹ : ↥(commV K))) : V) *
        (g : MulAut V) (((((⟨w, hw⟩ : ↥(commV K))⁻¹ : ↥(commV K))) : V))⁻¹,
        mul_mem (inv_mem hw) (apply_mem_commV_self K hg (inv_mem (inv_mem hw)))⟩ : ↥(commV K)) =
        ⟨g w * w⁻¹, Subgroup.subset_closure ⟨g, hg, w, rfl⟩⟩ := by
      apply Subtype.ext
      show w⁻¹ * g (w⁻¹)⁻¹ = g w * w⁻¹
      rw [inv_inv, mul_comm]
    rw [this] at hmem
    exact hmem
  have hinc : ∀ u : ↥(commV K), yuInc K u ∈ N := by
    intro u
    obtain ⟨u', hu', hu'u⟩ := hUK M₁ hMg u.2
    have : u' = u := Subtype.ext hu'u
    rw [← this]
    exact hu'
  rw [eq_top_iff]
  intro x _
  rw [yu_eq_inc_mul_sec K x]
  exact N.mul_mem (hinc _) (hsec _)

end Short

end CFSG.CGT.PushingUpLit.CGT6

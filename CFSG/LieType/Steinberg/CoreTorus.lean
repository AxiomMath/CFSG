module

public import CFSG.LieType.Steinberg.CoreUnipotent
public import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.LieType.Steinberg

namespace RootGroupData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {K : Type*} [Group K]
variable (D : RootGroupData Φ K)

@[expose] def stTorus (i : ι) : Subgroup (StGroup Φ D.X) :=
  D.stRankOne i ⊓ Subgroup.normalizer (D.stRoot (Pi.single i 1) : Set (StGroup Φ D.X)) ⊓
    Subgroup.normalizer (D.stRoot (-Pi.single i 1) : Set (StGroup Φ D.X))

@[expose] def stTorusPart : Subgroup (StGroup Φ D.X) := ⨆ i, D.stTorus i

@[expose] def IsSwap (i : ι) (g : StGroup Φ D.X) : Prop :=
  g ∈ D.stRankOne i ∧
    (D.stRoot (Pi.single i 1)).map (MulAut.conj g).toMonoidHom = D.stRoot (-Pi.single i 1) ∧
    (D.stRoot (-Pi.single i 1)).map (MulAut.conj g).toMonoidHom = D.stRoot (Pi.single i 1)

theorem stTorus_le_stRankOne (i : ι) : D.stTorus i ≤ D.stRankOne i :=
  inf_le_left.trans inf_le_left

theorem stTorus_le_normalizer_single (i : ι) :
    D.stTorus i ≤ Subgroup.normalizer (D.stRoot (Pi.single i 1) : Set (StGroup Φ D.X)) :=
  inf_le_left.trans inf_le_right

theorem stTorus_le_normalizer_neg_single (i : ι) :
    D.stTorus i ≤ Subgroup.normalizer (D.stRoot (-Pi.single i 1) : Set (StGroup Φ D.X)) :=
  inf_le_right

theorem stTorus_le_stTorusPart (i : ι) : D.stTorus i ≤ D.stTorusPart :=
  le_iSup D.stTorus i

theorem injOn_stTorus (i : ι) : Set.InjOn (stPi Φ D.X) (D.stTorus i) :=
  Set.InjOn.mono (fun _ hx => D.stTorus_le_stRankOne i hx) (D.injOn_stRankOne i)

theorem map_stTorus_le (i : ι) : (D.stTorus i).map (stPi Φ D.X) ≤ D.torus i := by
  have hα := Φ.single_mem i
  refine le_inf (le_inf ?_ ?_) ?_
  · exact (Subgroup.map_mono (D.stTorus_le_stRankOne i)).trans (D.map_stRankOne i).le
  · refine (Subgroup.map_mono (D.stTorus_le_normalizer_single i)).trans
      ((Subgroup.le_normalizer_map _).trans (le_of_eq ?_))
    rw [D.map_stRoot hα]
  · refine (Subgroup.map_mono (D.stTorus_le_normalizer_neg_single i)).trans
      ((Subgroup.le_normalizer_map _).trans (le_of_eq ?_))
    rw [D.map_stRoot (Φ.neg_mem _ hα)]

theorem stPi_mem_torus {i : ι} {h : StGroup Φ D.X} (hh : h ∈ D.stTorus i) :
    stPi Φ D.X h ∈ D.torus i :=
  D.map_stTorus_le i ⟨h, hh, rfl⟩

theorem stnw_mem {M : Subgroup (StGroup Φ D.X)} (h : ∀ i, D.stn i ∈ M) (w : List ι) :
    D.stnw w ∈ M :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact h j

theorem X_le_posPart {γ : ι → ℤ} (hγ : γ ∈ Φ.pos) : D.X γ ≤ D.posPart :=
  le_iSup₂ (f := fun γ (_ : γ ∈ Φ.pos) => D.X γ) γ hγ

theorem X_le_negPart {γ : ι → ℤ} (hγ : γ ∈ Φ.neg) : D.X γ ≤ D.negPart :=
  le_iSup₂ (f := fun γ (_ : γ ∈ Φ.neg) => D.X γ) γ hγ

variable {D}

theorem IsSwap.mul_mem {i : ι} {g g' : StGroup Φ D.X} (hg : D.IsSwap i g) (hg' : D.IsSwap i g') :
    g * g' ∈ D.stTorus i :=
  ⟨⟨Subgroup.mul_mem _ hg.1 hg'.1,
      mem_normalizer_iff_map_conj.2 (by rw [map_conj_mul, hg'.2.1, hg.2.2])⟩,
    mem_normalizer_iff_map_conj.2 (by rw [map_conj_mul, hg'.2.2, hg.2.1])⟩

theorem IsSwap.inv {i : ι} {g : StGroup Φ D.X} (hg : D.IsSwap i g) : D.IsSwap i g⁻¹ :=
  ⟨inv_mem hg.1, map_conj_inv_of_map_conj hg.2.2, map_conj_inv_of_map_conj hg.2.1⟩

theorem IsSwap.conj {i a : ι} {g c : StGroup Φ D.X} (hg : D.IsSwap i g)
    (h1 : (D.stRoot (Pi.single i 1)).map (MulAut.conj c).toMonoidHom = D.stRoot (Pi.single a 1))
    (h2 : (D.stRoot (-Pi.single i 1)).map (MulAut.conj c).toMonoidHom =
      D.stRoot (-Pi.single a 1)) :
    D.IsSwap a (c * g * c⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · have : (D.stRankOne i).map (MulAut.conj c).toMonoidHom = D.stRankOne a := by
      rw [stRankOne, Subgroup.map_sup, h1, h2, stRankOne]
    rw [← this]
    exact conj_mem_map_conj hg.1
  · rw [map_conj_mul, map_conj_mul, map_conj_inv_of_map_conj h1, hg.2.1, h2]
  · rw [map_conj_mul, map_conj_mul, map_conj_inv_of_map_conj h2, hg.2.2, h1]

namespace IsSteinberg

variable (hD : D.IsSteinberg)
include hD

theorem iSup_stRankOne_eq_top : ⨆ i, D.stRankOne i = ⊤ := by
  rw [eq_top_iff, ← D.stSub_roots, stSub_eq_iSup]
  have hw : ∀ w, D.stnw w ∈ ⨆ i, D.stRankOne i :=
    D.stnw_mem fun j => Subgroup.mem_iSup_of_mem j (hD.stn_mem j)
  have hind : ∀ δ ∈ Φ.roots, Φ.IsIndiv δ → D.stRoot δ ≤ ⨆ i, D.stRankOne i := by
    intro δ hδ hδ'
    obtain ⟨w, i, rfl⟩ := Φ.exists_word δ hδ hδ'
    rw [← hD.map_conj_stnw_stRoot w (Φ.single_mem i)]
    exact (Subgroup.map_mono ((D.stRoot_single_le_stRankOne i).trans (le_iSup _ i))).trans
      (map_conj_of_mem (hw w)).le
  refine iSup₂_le fun γ hγ => ?_
  by_cases h : Φ.IsIndiv γ
  · exact hind γ hγ h
  · obtain ⟨δ, hδ, hδ', rfl⟩ := Φ.exists_eq_two_smul hγ h
    exact (hD.stRoot_two_smul_le hδ hγ).trans (hind δ hδ hδ')

theorem stTorus_le_normalizer (i : ι) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    D.stTorus i ≤ Subgroup.normalizer (D.stRoot γ : Set (StGroup Φ D.X)) := by
  intro h hh
  rw [mem_normalizer_iff_map_conj]
  exact hD.map_conj_stRoot_eq (D.stTorus_le_stRankOne i hh) hγ hγ Iff.rfl Iff.rfl
    (mem_normalizer_iff_map_conj.1 (hD.torus_le_normalizer i γ hγ (D.stPi_mem_torus hh)))

theorem map_stTorus (i : ι) : (D.stTorus i).map (stPi Φ D.X) = D.torus i := by
  have hα := Φ.single_mem i
  have hα' := Φ.neg_mem _ hα
  refine le_antisymm (D.map_stTorus_le i) fun t ht => ?_
  have htL : t ∈ D.rankOne i := ht.1.1
  rw [← D.map_stRankOne] at htL
  obtain ⟨g, hg, rfl⟩ := htL
  have h1 : g ∈ Subgroup.normalizer (D.stRoot (Pi.single i 1) : Set (StGroup Φ D.X)) :=
    mem_normalizer_iff_map_conj.2 (hD.map_conj_stRoot_eq hg hα hα Iff.rfl Iff.rfl
      (mem_normalizer_iff_map_conj.1 ht.1.2))
  have h2 : g ∈ Subgroup.normalizer (D.stRoot (-Pi.single i 1) : Set (StGroup Φ D.X)) :=
    mem_normalizer_iff_map_conj.2 (hD.map_conj_stRoot_eq hg hα' hα' Iff.rfl Iff.rfl
      (mem_normalizer_iff_map_conj.1 ht.2))
  exact ⟨g, ⟨⟨hg, h1⟩, h2⟩, rfl⟩

theorem exists_mem_stTorus {i : ι} {t : K} (ht : t ∈ D.torus i) :
    ∃ h ∈ D.stTorus i, stPi Φ D.X h = t := by
  rw [← hD.map_stTorus] at ht
  exact ht

theorem map_conj_stn_mul_stn (i : ι) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    (D.stRoot γ).map (MulAut.conj (D.stn i * D.stn i)).toMonoidHom = D.stRoot γ := by
  rw [map_conj_mul, hD.map_conj_stn_stRoot i hγ, hD.map_conj_stn_stRoot i (Φ.refl_mem i γ hγ),
    Φ.refl_refl]

theorem stn_mul_stn_mem (i : ι) : D.stn i * D.stn i ∈ D.stTorus i :=
  ⟨⟨mul_mem (hD.stn_mem i) (hD.stn_mem i),
      mem_normalizer_iff_map_conj.2 (hD.map_conj_stn_mul_stn i (Φ.single_mem i))⟩,
    mem_normalizer_iff_map_conj.2 (hD.map_conj_stn_mul_stn i (Φ.neg_mem _ (Φ.single_mem i)))⟩

theorem isSwap_stn (i : ι) : D.IsSwap i (D.stn i) :=
  ⟨hD.stn_mem i, by rw [hD.map_conj_stn_stRoot i (Φ.single_mem i), Φ.refl_single],
    by rw [hD.map_conj_stn_stRoot i (Φ.neg_mem _ (Φ.single_mem i)), Φ.refl_neg_single]⟩

theorem exists_eq_n_mul {i : ι} {g : K} (hg : g ∈ D.rankOne i)
    (h1 : (D.X (Pi.single i 1)).map (MulAut.conj g).toMonoidHom = D.X (-Pi.single i 1))
    (h2 : (D.X (-Pi.single i 1)).map (MulAut.conj g).toMonoidHom = D.X (Pi.single i 1)) :
    ∃ t ∈ D.torus i, g = D.n i * t := by
  have hα := Φ.single_mem i
  have hα' := Φ.neg_mem _ hα
  have hn1 : (D.X (Pi.single i 1)).map (MulAut.conj (D.n i)).toMonoidHom =
      D.X (-Pi.single i 1) := by
    rw [hD.map_conj_n i _ hα, Φ.refl_single]
  have hn2 : (D.X (-Pi.single i 1)).map (MulAut.conj (D.n i)).toMonoidHom =
      D.X (Pi.single i 1) := by
    rw [hD.map_conj_n i _ hα', Φ.refl_neg_single]
  rcases hD.rankOne_bruhat i g hg with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
  · exfalso
    rw [map_conj_mul, map_conj_of_mem hu, mem_normalizer_iff_map_conj.1 hh.1.2] at h1
    apply hD.ne_bot _ hα
    rw [eq_bot_iff, ← hD.posPart_inf_negPart]
    refine le_inf (D.X_le_posPart (Φ.single_mem_pos i)) ?_
    rw [h1]
    exact D.X_le_negPart (Φ.neg_single_mem_neg i)
  · rw [map_conj_mul, map_conj_mul, map_conj_mul, map_conj_of_mem hv,
      mem_normalizer_iff_map_conj.1 hh.1.2, hn1] at h1
    obtain rfl : u = 1 := hD.eq_one_of_mem_normalizer i u hu (mem_normalizer_iff_map_conj.2 h1)
    rw [one_mul, map_conj_mul, map_conj_mul, ← hn2] at h2
    have h2' := Subgroup.map_injective (MulAut.conj (D.n i)).injective h2
    have h3 : (D.X (-Pi.single i 1)).map (MulAut.conj v).toMonoidHom = D.X (-Pi.single i 1) := by
      rw [← map_conj_inv_of_map_conj h2']
      exact map_conj_inv_of_map_conj (mem_normalizer_iff_map_conj.1 hh.2)
    obtain rfl : v = 1 := hD.eq_one_of_mem_normalizer i v hv (mem_normalizer_iff_map_conj.2 h3)
    exact ⟨h, hh, by rw [mul_one, one_mul]⟩

theorem exists_eq_stn_mul {i : ι} {g : StGroup Φ D.X} (hg : D.IsSwap i g) :
    ∃ h ∈ D.stTorus i, g = D.stn i * h := by
  have hα := Φ.single_mem i
  have hα' := Φ.neg_mem _ hα
  have hK : ∀ {γ δ : ι → ℤ}, γ ∈ Φ.roots → δ ∈ Φ.roots →
      (D.stRoot γ).map (MulAut.conj g).toMonoidHom = D.stRoot δ →
      (D.X γ).map (MulAut.conj (stPi Φ D.X g)).toMonoidHom = D.X δ := by
    intro γ δ hγ hδ h
    rw [← D.map_stRoot hγ, ← map_map_conj, h, D.map_stRoot hδ]
  have hgK : stPi Φ D.X g ∈ D.rankOne i := by
    rw [← D.map_stRankOne]
    exact Subgroup.mem_map_of_mem _ hg.1
  obtain ⟨t, ht, hgt⟩ := hD.exists_eq_n_mul hgK (hK hα hα' hg.2.1) (hK hα' hα hg.2.2)
  obtain ⟨h, hh, rfl⟩ := hD.exists_mem_stTorus ht
  refine ⟨h, hh, D.injOn_stRankOne i hg.1
    (mul_mem (hD.stn_mem i) (D.stTorus_le_stRankOne i hh)) ?_⟩
  rw [map_mul, hD.stPi_stn, hgt]

theorem stTorus_le_normalizer_stRankOne (i j : ι) :
    D.stTorus i ≤ Subgroup.normalizer (D.stRankOne j : Set (StGroup Φ D.X)) :=
  le_normalizer_sup (hD.stTorus_le_normalizer i (Φ.single_mem j))
    (hD.stTorus_le_normalizer i (Φ.neg_mem _ (Φ.single_mem j)))

theorem commute_of_mem_stTorus {i j : ι} {h h' : StGroup Φ D.X} (hh : h ∈ D.stTorus i)
    (hh' : h' ∈ D.stTorus j) : Commute h h' := by
  have hmem : h * h' * h⁻¹ ∈ D.stRankOne j := by
    rw [← mem_normalizer_iff_map_conj.1 (hD.stTorus_le_normalizer_stRankOne i j hh)]
    exact conj_mem_map_conj (D.stTorus_le_stRankOne j hh')
  have heq : h * h' * h⁻¹ = h' := by
    refine D.injOn_stRankOne j hmem (D.stTorus_le_stRankOne j hh') ?_
    rw [map_mul, map_mul, map_inv,
      (hD.torus_commute i j _ (D.stPi_mem_torus hh) _ (D.stPi_mem_torus hh')).eq,
      mul_inv_cancel_right]
  calc h * h' = h * h' * h⁻¹ * h := by group
    _ = h' * h := by rw [heq]

theorem map_stTorusPart : D.stTorusPart.map (stPi Φ D.X) = D.torusPart := by
  rw [stTorusPart, Subgroup.map_iSup, torusPart]
  exact iSup_congr fun i => hD.map_stTorus i

theorem injOn_stTorusPart : Set.InjOn (stPi Φ D.X) D.stTorusPart := by
  have hcomm : Pairwise fun i j => ∀ x y : StGroup Φ D.X, x ∈ D.stTorus i → y ∈ D.stTorus j →
      Commute x y := fun i j _ x y hx hy => hD.commute_of_mem_stTorus hx hy
  refine injOn_of_eq_one fun g hg h1 => ?_
  rw [stTorusPart, ← Subgroup.noncommPiCoprod_range (hcomm := hcomm)] at hg
  obtain ⟨u, rfl⟩ := hg
  rw [Subgroup.noncommPiCoprod_apply] at h1
  have h1' := (Finset.map_noncommProd _ _ _ (stPi Φ D.X)).symm.trans h1
  have hu := Subgroup.eq_one_of_noncommProd_eq_one_of_iSupIndep _ _ _ D.torus
    hD.torus_iSupIndep (fun i _ => D.stPi_mem_torus (u i).2) h1'
  have hu1 : u = 1 := funext fun i => Subtype.ext <| D.injOn_stTorus i (u i).2 (one_mem _)
    (by simpa using hu i (Finset.mem_univ i))
  rw [hu1, map_one]

theorem stTorusPart_le_normalizer {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    D.stTorusPart ≤ Subgroup.normalizer (D.stRoot γ : Set (StGroup Φ D.X)) :=
  iSup_le fun i => hD.stTorus_le_normalizer i hγ

theorem stTorusPart_le_normalizer_stRankOne (i : ι) :
    D.stTorusPart ≤ Subgroup.normalizer (D.stRankOne i : Set (StGroup Φ D.X)) :=
  iSup_le fun j => hD.stTorus_le_normalizer_stRankOne j i

theorem stn_mem_normalizer (i : ι) :
    D.stn i ∈ Subgroup.normalizer (D.stTorusPart : Set (StGroup Φ D.X)) := by
  have hα := Φ.single_mem i
  have hle : D.stTorusPart.map (MulAut.conj (D.stn i)).toMonoidHom ≤ D.stTorusPart := by
    rw [stTorusPart, Subgroup.map_iSup]
    refine iSup_le fun j => map_conj_le_iff.2 fun c hc => ?_
    have hs : D.IsSwap i (c * (D.stn i)⁻¹ * c⁻¹) := (hD.isSwap_stn i).inv.conj
      (mem_normalizer_iff_map_conj.1 (hD.stTorus_le_normalizer j hα hc))
      (mem_normalizer_iff_map_conj.1 (hD.stTorus_le_normalizer j (Φ.neg_mem _ hα) hc))
    have : D.stn i * c * (D.stn i)⁻¹ = D.stn i * (c * (D.stn i)⁻¹ * c⁻¹) * c := by group
    rw [this]
    exact mul_mem (Subgroup.mem_iSup_of_mem i ((hD.isSwap_stn i).mul_mem hs))
      (Subgroup.mem_iSup_of_mem j hc)
  rw [mem_normalizer_iff_map_conj]
  refine le_antisymm hle fun x hx => ?_
  have hnn : D.stn i * D.stn i ∈ D.stTorusPart :=
    D.stTorus_le_stTorusPart i (hD.stn_mul_stn_mem i)
  have h2 : D.stn i * x * (D.stn i)⁻¹ ∈ D.stTorusPart := hle ⟨x, hx, rfl⟩
  refine ⟨(D.stn i)⁻¹ * x * D.stn i, ?_, ?_⟩
  · have : (D.stn i)⁻¹ * x * D.stn i =
        (D.stn i * D.stn i)⁻¹ * (D.stn i * x * (D.stn i)⁻¹) * (D.stn i * D.stn i) := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hnn) h2) hnn
  · change D.stn i * ((D.stn i)⁻¹ * x * D.stn i) * (D.stn i)⁻¹ = x
    group

theorem stnw_mem_normalizer (w : List ι) :
    D.stnw w ∈ Subgroup.normalizer (D.stTorusPart : Set (StGroup Φ D.X)) :=
  D.stnw_mem (hD.stn_mem_normalizer) w

end IsSteinberg

end RootGroupData

end CFSG.LieType.Steinberg

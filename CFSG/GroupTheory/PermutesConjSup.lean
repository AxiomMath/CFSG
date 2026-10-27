module

public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {H : Type*} [Group H]

theorem map_conj_eq_of_map_conj_eq {K T B : Subgroup H} {u v : H} (hu : u ∈ T) (hv : v ∈ T)
    (hB : ∀ z ∈ T, K.map (MulAut.conj z).toMonoidHom = K →
      B.map (MulAut.conj z).toMonoidHom = B)
    (hK : K.map (MulAut.conj u).toMonoidHom = K.map (MulAut.conj v).toMonoidHom) :
    B.map (MulAut.conj u).toMonoidHom = B.map (MulAut.conj v).toMonoidHom := by
  have hzT : v⁻¹ * u ∈ T := T.mul_mem (T.inv_mem hv) hu
  have hzK : K.map (MulAut.conj (v⁻¹ * u)).toMonoidHom = K := by
    calc K.map (MulAut.conj (v⁻¹ * u)).toMonoidHom
        = (K.map (MulAut.conj u).toMonoidHom).map (MulAut.conj v⁻¹).toMonoidHom := by
          rw [map_conj_map_conj]
      _ = (K.map (MulAut.conj v).toMonoidHom).map (MulAut.conj v⁻¹).toMonoidHom := by rw [hK]
      _ = K.map (MulAut.conj (v⁻¹ * v)).toMonoidHom := by rw [map_conj_map_conj]
      _ = K := by rw [inv_mul_cancel, map_one]; exact Subgroup.map_id K
  have hBz : B.map (MulAut.conj (v⁻¹ * u)).toMonoidHom = B := hB _ hzT hzK
  calc B.map (MulAut.conj u).toMonoidHom
      = (B.map (MulAut.conj (v⁻¹ * u)).toMonoidHom).map (MulAut.conj v).toMonoidHom := by
        rw [map_conj_map_conj]
        congr 1
        group
    _ = B.map (MulAut.conj v).toMonoidHom := by rw [hBz]

theorem commute_of_mem_map_conj_of_ne {K T : Subgroup H}
    (hcomm : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom ≠ K →
      ∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj t).toMonoidHom, Commute x y)
    {u v : H} (hu : u ∈ T) (hv : v ∈ T)
    (hne : K.map (MulAut.conj u).toMonoidHom ≠ K.map (MulAut.conj v).toMonoidHom) :
    ∀ x ∈ K.map (MulAut.conj u).toMonoidHom,
      ∀ y ∈ K.map (MulAut.conj v).toMonoidHom, Commute x y := by
  intro x hx y hy
  have ht : u⁻¹ * v ∈ T := T.mul_mem (T.inv_mem hu) hv
  have hKt : K.map (MulAut.conj (u⁻¹ * v)).toMonoidHom ≠ K := by
    intro hEq
    apply hne
    calc K.map (MulAut.conj u).toMonoidHom
        = (K.map (MulAut.conj (u⁻¹ * v)).toMonoidHom).map
            (MulAut.conj u).toMonoidHom := by rw [hEq]
      _ = K.map (MulAut.conj (u * (u⁻¹ * v))).toMonoidHom := by
          rw [map_conj_map_conj]
      _ = K.map (MulAut.conj v).toMonoidHom := by
          congr 1
          group
  obtain ⟨x₀, hx₀, hxx⟩ := Subgroup.mem_map.mp hx
  obtain ⟨y₀, hy₀, hyy⟩ := Subgroup.mem_map.mp hy
  have hx' : (MulAut.conj u)⁻¹ x ∈ K := by
    rw [← hxx]
    change (MulAut.conj u)⁻¹ ((MulAut.conj u) x₀) ∈ K
    have h : (MulAut.conj u)⁻¹ ((MulAut.conj u) x₀) = x₀ := by
      simp only [MulAut.conj_inv_apply, MulAut.conj_apply]
      group
    rw [h]
    exact hx₀
  have hy' : (MulAut.conj u)⁻¹ y ∈ K.map (MulAut.conj (u⁻¹ * v)).toMonoidHom := by
    have hconj : (MulAut.conj u)⁻¹ y = (MulAut.conj (u⁻¹ * v)).toMonoidHom y₀ := by
      rw [← hyy]
      change (MulAut.conj u)⁻¹ ((MulAut.conj v) y₀) = (MulAut.conj (u⁻¹ * v)) y₀
      simp only [MulAut.conj_inv_apply, MulAut.conj_apply]
      group
    rw [hconj]
    exact Subgroup.mem_map_of_mem _ hy₀
  have hc : Commute ((MulAut.conj u)⁻¹ x) ((MulAut.conj u)⁻¹ y) :=
    hcomm _ ht hKt _ hx' _ hy'
  have := hc.map (MulAut.conj u).toMonoidHom
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem exists_permutes_sup_conj {H : Type*} [Group H] [Finite H] {K T A : Subgroup H}
    (hAK : A ≤ K)
    (hcomm : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom ≠ K →
      ∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj t).toMonoidHom, Commute x y)
    (hperm : (A : Set H) * ((T ⊓ normalizer (K : Set H) : Subgroup H) : Set H) =
      ((T ⊓ normalizer (K : Set H) : Subgroup H) : Set H) * A) :
    ∃ X : Subgroup H, A ≤ X ∧ (X : Set H) * T = T * X ∧
      (∀ n : ℕ, (∀ a ∈ A, a ^ n = 1) → ∀ x ∈ X, x ^ n = 1) ∧
      (∀ p : ℕ, IsPGroup p A → IsPGroup p X) := by
  classical
  let S : Subgroup H := T ⊓ normalizer (K : Set H)
  let W : Subgroup H :=
    { carrier := (A : Set H) * (S : Set H)
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, s₁, hs₁, rfl⟩ ⟨a₂, ha₂, s₂, hs₂, rfl⟩
        have hmem : s₁ * a₂ ∈ (A : Set H) * (S : Set H) := by
          have h' : s₁ * a₂ ∈ (S : Set H) * (A : Set H) := ⟨s₁, hs₁, a₂, ha₂, rfl⟩
          rwa [← hperm] at h'
        obtain ⟨a₃, ha₃, s₃, hs₃, hEq⟩ := Set.mem_mul.mp hmem
        refine ⟨a₁ * a₃, A.mul_mem ha₁ ha₃, s₃ * s₂, S.mul_mem hs₃ hs₂, ?_⟩
        calc (a₁ * a₃) * (s₃ * s₂) = a₁ * (a₃ * s₃) * s₂ := by group
          _ = a₁ * (s₁ * a₂) * s₂ := by rw [hEq]
          _ = (a₁ * s₁) * (a₂ * s₂) := by group
      one_mem' := ⟨1, A.one_mem, 1, S.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, s, hs, rfl⟩
        have hmem : s⁻¹ * a⁻¹ ∈ (S : Set H) * (A : Set H) :=
          ⟨s⁻¹, S.inv_mem hs, a⁻¹, A.inv_mem ha, rfl⟩
        rw [← hperm] at hmem
        obtain ⟨a', ha', s', hs', hEq⟩ := Set.mem_mul.mp hmem
        exact ⟨a', ha', s', hs', by
          calc a' * s' = s⁻¹ * a⁻¹ := hEq
            _ = (a * s)⁻¹ := by group⟩ }
  let B₁ : Subgroup H := W ⊓ K
  have hS_le_W : S ≤ W := by
    intro s hs
    exact ⟨1, A.one_mem, s, hs, one_mul s⟩
  have hSK : S ⊓ K = T ⊓ K := by
    show T ⊓ normalizer (K : Set H) ⊓ K = T ⊓ K
    rw [inf_assoc, inf_eq_right.mpr (Subgroup.le_normalizer)]
  have hB₁S : (B₁ : Set H) = ((S ⊓ K : Subgroup H) : Set H) * (A : Set H) := by
    have h := Subgroup.inf_mul_assoc K S A hAK
    calc (B₁ : Set H) = ((A : Set H) * (S : Set H)) ∩ (K : Set H) := rfl
      _ = ((S : Set H) * (A : Set H)) ∩ (K : Set H) := by rw [hperm]
      _ = (K : Set H) ∩ ((S : Set H) * (A : Set H)) := Set.inter_comm _ _
      _ = ((K ⊓ S : Subgroup H) : Set H) * (A : Set H) := h.symm
      _ = ((S ⊓ K : Subgroup H) : Set H) * (A : Set H) := by rw [inf_comm]
  have hB₁norm : ∀ z ∈ T, K.map (MulAut.conj z).toMonoidHom = K →
      B₁.map (MulAut.conj z).toMonoidHom = B₁ := by
    intro z hzT hzK
    have hzS : z ∈ S := by
      refine ⟨hzT, ?_⟩
      change z ∈ normalizer (K : Set H)
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hzW : z ∈ W := hS_le_W hzS
    have hWz : W.map (MulAut.conj z).toMonoidHom = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hzW)
    calc B₁.map (MulAut.conj z).toMonoidHom
        = (W ⊓ K).map (MulAut.conj z).toMonoidHom := rfl
      _ = W.map (MulAut.conj z).toMonoidHom ⊓ K.map (MulAut.conj z).toMonoidHom :=
            Subgroup.map_inf_eq _ _ _ (MulAut.conj z).injective
      _ = W ⊓ K := by rw [hWz, hzK]
      _ = B₁ := rfl
  let f : H → Subgroup H := fun t => K.map (MulAut.conj t).toMonoidHom
  let orb : Set (Subgroup H) := {K' | ∃ t : H, t ∈ T ∧ f t = K'}
  let ι := ↥orb
  have hfin : orb.Finite := by
    have h : orb = f '' (T : Set H) := by
      ext K'
      simp [orb]
    rw [h]
    exact (Set.toFinite (T : Set H)).image f
  letI : Fintype ι := Set.Finite.fintype hfin
  let tOf : ι → H := fun i =>
    if h : (i : Subgroup H) = K then 1
    else Classical.choose (show ∃ t : H, t ∈ T ∧ f t = (i : Subgroup H) from i.2)
  have tOf_mem : ∀ i, tOf i ∈ T := by
    intro i
    by_cases h : (i : Subgroup H) = K
    · simp [tOf, h]
    · have hs := (Classical.choose_spec
        (show ∃ t : H, t ∈ T ∧ f t = (i : Subgroup H) from i.2)).1
      simpa [tOf, h] using hs
  have tOf_conj : ∀ i, K.map (MulAut.conj (tOf i)).toMonoidHom = (i : Subgroup H) := by
    intro i
    by_cases h : (i : Subgroup H) = K
    · rw [h, show tOf i = 1 from by simp [tOf, h]]
      rw [map_one]; exact Subgroup.map_id K
    · have hs := (Classical.choose_spec
        (show ∃ t : H, t ∈ T ∧ f t = (i : Subgroup H) from i.2)).2
      simpa [tOf, h, f] using hs
  let i₀ : ι := ⟨K, ⟨1, T.one_mem, by simp only [f, map_one]; exact Subgroup.map_id K⟩⟩
  have tOf_i₀ : tOf i₀ = 1 := by
    unfold tOf
    rw [dif_pos rfl]
  let AOf : ι → Subgroup H := fun i => A.map (MulAut.conj (tOf i)).toMonoidHom
  let Cof : ι → Subgroup H := fun i => B₁.map (MulAut.conj (tOf i)).toMonoidHom
  let Rof : ι → Subgroup H := fun i => T ⊓ (i : Subgroup H)
  let X : Subgroup H := ⨆ i, AOf i
  let R : Subgroup H := ⨆ i, Rof i
  let B : Subgroup H := ⨆ i, Cof i
  have hmapTK : ∀ i, (T ⊓ K).map (MulAut.conj (tOf i)).toMonoidHom = Rof i := by
    intro i
    show (T ⊓ K).map (MulAut.conj (tOf i)).toMonoidHom = T ⊓ (i : Subgroup H)
    have hTi : T.map (MulAut.conj (tOf i)).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (tOf_mem i))
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (tOf i)).injective, hTi, tOf_conj i]
  have hCsplit : ∀ i, (Cof i : Set H) = (Rof i : Set H) * (AOf i : Set H) := by
    intro i
    calc (Cof i : Set H)
        = (MulAut.conj (tOf i)).toMonoidHom '' (B₁ : Set H) := Subgroup.coe_map _ _
      _ = (MulAut.conj (tOf i)).toMonoidHom ''
            (((S ⊓ K : Subgroup H) : Set H) * (A : Set H)) := by rw [hB₁S]
      _ = ((MulAut.conj (tOf i)).toMonoidHom '' ((S ⊓ K : Subgroup H) : Set H)) *
            ((MulAut.conj (tOf i)).toMonoidHom '' (A : Set H)) := Set.image_mul _
      _ = ((MulAut.conj (tOf i)).toMonoidHom '' ((T ⊓ K : Subgroup H) : Set H)) *
            ((MulAut.conj (tOf i)).toMonoidHom '' (A : Set H)) := by rw [hSK]
      _ = (Rof i : Set H) * (AOf i : Set H) := by
            rw [← hmapTK i, Subgroup.coe_map, Subgroup.coe_map]
  have hKpair : ∀ i j : ι, i ≠ j → ∀ x ∈ (i : Subgroup H), ∀ y ∈ (j : Subgroup H), Commute x y := by
    intro i j hij x hx y hy
    have hne : (i : Subgroup H) ≠ (j : Subgroup H) := fun h => hij (Subtype.ext h)
    have hne' : K.map (MulAut.conj (tOf i)).toMonoidHom ≠
        K.map (MulAut.conj (tOf j)).toMonoidHom := by
      rw [tOf_conj i, tOf_conj j]
      exact hne
    have hx' : x ∈ K.map (MulAut.conj (tOf i)).toMonoidHom := by rwa [tOf_conj i]
    have hy' : y ∈ K.map (MulAut.conj (tOf j)).toMonoidHom := by rwa [tOf_conj j]
    exact commute_of_mem_map_conj_of_ne hcomm (tOf_mem i) (tOf_mem j) hne' x hx' y hy'
  have hpairA : Pairwise fun i j : ι => ∀ x y : H, x ∈ AOf i → y ∈ AOf j → Commute x y := by
    intro i j hij x y hx hy
    have hx' : x ∈ (i : Subgroup H) := by
      rw [← tOf_conj i]; exact Subgroup.map_mono hAK hx
    have hy' : y ∈ (j : Subgroup H) := by
      rw [← tOf_conj j]; exact Subgroup.map_mono hAK hy
    exact hKpair i j hij x hx' y hy'
  have hB₁_le_K : B₁ ≤ K := inf_le_right
  have hpairC : Pairwise fun i j : ι => ∀ x y : H, x ∈ Cof i → y ∈ Cof j → Commute x y := by
    intro i j hij x y hx hy
    have hx' : x ∈ (i : Subgroup H) := by
      rw [← tOf_conj i]; exact Subgroup.map_mono hB₁_le_K hx
    have hy' : y ∈ (j : Subgroup H) := by
      rw [← tOf_conj j]; exact Subgroup.map_mono hB₁_le_K hy
    exact hKpair i j hij x hx' y hy'

  let ΦA : ((i : ι) → AOf i) →* H := Subgroup.noncommPiCoprod hpairA
  let ΦC : ((i : ι) → Cof i) →* H := Subgroup.noncommPiCoprod hpairC
  have hXrange : ΦA.range = X := Subgroup.noncommPiCoprod_range
  have hBrange : ΦC.range = B := Subgroup.noncommPiCoprod_range
  have hAOf_i₀ : AOf i₀ = A := by
    show A.map (MulAut.conj (tOf i₀)).toMonoidHom = A
    rw [tOf_i₀]
    rw [map_one]; exact Subgroup.map_id A
  have hA_le_X : A ≤ X := by
    calc A = AOf i₀ := hAOf_i₀.symm
      _ ≤ X := le_iSup AOf i₀
  have hRleT : R ≤ T := iSup_le fun i => inf_le_left
  have hRof_le_Cof : ∀ i, Rof i ≤ Cof i := by
    intro i x hx
    have hx' : x ∈ (Rof i : Set H) * (AOf i : Set H) :=
      ⟨x, hx, 1, (AOf i).one_mem, mul_one x⟩
    rwa [← hCsplit i] at hx'
  have hAof_le_Cof : ∀ i, AOf i ≤ Cof i := by
    intro i x hx
    have hx' : x ∈ (Rof i : Set H) * (AOf i : Set H) :=
      ⟨1, (Rof i).one_mem, x, hx, one_mul x⟩
    rwa [← hCsplit i] at hx'
  have hRleB : R ≤ B := iSup_le fun i => (hRof_le_Cof i).trans (le_iSup Cof i)
  have hXleB : X ≤ B := iSup_le fun i => (hAof_le_Cof i).trans (le_iSup Cof i)
  have hRXB : (R : Set H) * (X : Set H) = (B : Set H) := by
    apply Set.Subset.antisymm
    · rintro z ⟨r, hr, x, hx, rfl⟩
      exact B.mul_mem (hRleB hr) (hXleB hx)
    · intro b hb
      have hb' : b ∈ ΦC.range := hBrange ▸ hb
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hb'
      have hdec : ∀ i : ι, ∃ r a : H, r ∈ Rof i ∧ a ∈ AOf i ∧ (u i : H) = r * a := by
        intro i
        have hu : (u i : H) ∈ (Cof i : Set H) := (u i).2
        rw [hCsplit i] at hu
        obtain ⟨r, hr, a, ha, hra⟩ := Set.mem_mul.mp hu
        exact ⟨r, a, hr, ha, hra.symm⟩
      choose rf af hrf haf hua using hdec
      have hcommR : (((Finset.univ : Finset ι)) : Set ι).Pairwise (Function.onFun Commute rf) := by
        intro i _ j _ hij
        exact hKpair i j hij (rf i) (hrf i).2 (rf j) (hrf j).2
      have hcommA' : (((Finset.univ : Finset ι)) : Set ι).Pairwise (Function.onFun Commute af) := by
        intro i _ j _ hij
        have hi : af i ∈ (i : Subgroup H) := by
          rw [← tOf_conj i]; exact Subgroup.map_mono hAK (haf i)
        have hj : af j ∈ (j : Subgroup H) := by
          rw [← tOf_conj j]; exact Subgroup.map_mono hAK (haf j)
        exact hKpair i j hij (af i) hi (af j) hj
      have hcommRA : (((Finset.univ : Finset ι)) : Set ι).Pairwise fun i j => Commute (af i) (rf j) := by
        intro i _ j _ hij
        have hi : af i ∈ (i : Subgroup H) := by
          rw [← tOf_conj i]; exact Subgroup.map_mono hAK (haf i)
        exact hKpair i j hij (af i) hi (rf j) (hrf j).2
      have hprod : ΦC u = (Finset.univ.noncommProd rf hcommR) *
          (Finset.univ.noncommProd af hcommA') := by
        calc ΦC u
            = Finset.univ.noncommProd (fun i => (u i : H)) _ :=
                Subgroup.noncommPiCoprod_apply hpairC u
          _ = Finset.univ.noncommProd (fun i => rf i * af i) _ :=
                Finset.noncommProd_congr rfl (fun i _ => hua i) _
          _ = (Finset.univ.noncommProd rf hcommR) *
                (Finset.univ.noncommProd af hcommA') :=
                Finset.noncommProd_mul_distrib rf af hcommR hcommA' hcommRA
      rw [hprod]
      refine ⟨Finset.univ.noncommProd rf hcommR, ?_,
        Finset.univ.noncommProd af hcommA', ?_, rfl⟩
      · exact Subgroup.noncommProd_mem R hcommR fun i _ => le_iSup Rof i (hrf i)
      · exact Subgroup.noncommProd_mem X hcommA' fun i _ => le_iSup AOf i (haf i)
  have hle_apply : ∀ s ∈ T, B.map (MulAut.conj s).toMonoidHom ≤ B := by
    intro s hs
    dsimp only [B]
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    have h1 : (Cof i).map (MulAut.conj s).toMonoidHom =
        B₁.map (MulAut.conj (s * tOf i)).toMonoidHom := by
      rw [show Cof i = B₁.map (MulAut.conj (tOf i)).toMonoidHom from rfl,
        map_conj_map_conj]
    rw [h1]
    let j : ι := ⟨K.map (MulAut.conj (s * tOf i)).toMonoidHom,
      ⟨s * tOf i, T.mul_mem hs (tOf_mem i), rfl⟩⟩
    have hj : B₁.map (MulAut.conj (s * tOf i)).toMonoidHom = Cof j :=
      map_conj_eq_of_map_conj_eq (T.mul_mem hs (tOf_mem i)) (tOf_mem j) hB₁norm
        (tOf_conj j).symm
    rw [hj]
    exact le_iSup Cof j
  have hBinv : ∀ s ∈ T, B.map (MulAut.conj s).toMonoidHom = B := by
    intro s hs
    apply le_antisymm (hle_apply s hs)
    have h := hle_apply s⁻¹ (T.inv_mem hs)
    calc B = (B.map (MulAut.conj s⁻¹).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
          rw [map_conj_map_conj, show s * s⁻¹ = 1 by group, map_one]; exact (Subgroup.map_id B).symm
      _ ≤ B.map (MulAut.conj s).toMonoidHom := Subgroup.map_mono h
  have hTB : T ≤ normalizer (B : Set H) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa using hBinv s hs
  have hpermute : (X : Set H) * (T : Set H) = (T : Set H) * (X : Set H) := by
    have hconj : ∀ t ∈ T, ∀ x ∈ B, t * x * t⁻¹ ∈ B := fun t ht x hx =>
      (Subgroup.mem_normalizer_iff.1 (hTB ht) x).1 hx
    have hSA : ∀ x ∈ B, ∃ s ∈ R, ∃ a ∈ X, x = s * a := by
      intro x hx
      have hx' : x ∈ (R : Set H) * (X : Set H) := hRXB.symm ▸ hx
      obtain ⟨s, hs, a, ha, hsa⟩ := Set.mem_mul.mp hx'
      exact ⟨s, hs, a, ha, hsa.symm⟩
    have hAS : ∀ x ∈ B, ∃ a ∈ X, ∃ s ∈ R, x = a * s := by
      intro x hx
      have hxinv : x⁻¹ ∈ (R : Set H) * (X : Set H) := by
        rw [hRXB]
        exact B.inv_mem hx
      obtain ⟨s, hs, a, ha, hsa⟩ := Set.mem_mul.mp hxinv
      exact ⟨a⁻¹, X.inv_mem ha, s⁻¹, R.inv_mem hs, by
        have h1 : x = (s * a)⁻¹ := by rw [hsa, inv_inv]
        rw [h1, mul_inv_rev]⟩
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, t, ht, rfl⟩
      have hxB : x ∈ B := hXleB hx
      obtain ⟨s, hs, a, ha, hsta⟩ := hSA (t⁻¹ * x * t) (by
        simpa using hconj t⁻¹ (T.inv_mem ht) x hxB)
      refine ⟨t * s, T.mul_mem ht (hRleT hs), a, ha, ?_⟩
      calc t * s * a = t * (s * a) := by rw [mul_assoc]
        _ = t * (t⁻¹ * x * t) := by rw [← hsta]
        _ = x * t := by group
    · rintro z ⟨t, ht, x, hx, rfl⟩
      have hxB : x ∈ B := hXleB hx
      obtain ⟨a, ha, s, hs, hats⟩ := hAS (t * x * t⁻¹) (hconj t ht x hxB)
      refine ⟨a, ha, s * t, T.mul_mem (hRleT hs) ht, ?_⟩
      calc a * (s * t) = (a * s) * t := by rw [mul_assoc]
        _ = (t * x * t⁻¹) * t := by rw [← hats]
        _ = t * x := by group
  refine ⟨X, hA_le_X, hpermute, ?_, ?_⟩
  · intro n hn x hx
    have hexpA : ∀ i : ι, Monoid.exponent ↥(AOf i) ∣ n := by
      intro i
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp a.2
      rw [← hba, ← map_pow, hn b hb, map_one]
    have hexpPi : Monoid.exponent ((i : ι) → ↥(AOf i)) ∣ n := by
      rw [Monoid.exponent_pi]
      exact Finset.lcm_dvd fun i _ => hexpA i
    have hxr : x ∈ ΦA.range := hXrange ▸ hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hxr
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexpPi u, map_one]
  · intro p hp
    have hAiP : ∀ i : ι, IsPGroup p ↥(AOf i) := fun i =>
      IsPGroup.map hp (MulAut.conj (tOf i)).toMonoidHom
    have hPiP : IsPGroup p ((i : ι) → ↥(AOf i)) := IsPGroup.pi hAiP
    have hTopP : IsPGroup p ↥(⊤ : Subgroup ((i : ι) → ↥(AOf i))) :=
      hPiP.of_equiv Subgroup.topEquiv.symm
    have hmap := IsPGroup.map hTopP ΦA
    rw [Subgroup.map_top] at hmap
    exact hXrange ▸ hmap

end CFSG.GroupTheory

end


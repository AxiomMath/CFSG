module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore map_centralizerPerfectCore)

section Blocks

variable {n : ℕ} {K : Type*} [Field K] {F : Type*} [Field F]

theorem map_blockComplProj (ι : K →+* F) (I : Finset (Fin n)) :
    (blockComplProj (K := K) I).map ι = blockComplProj (K := F) I := by
  rw [blockComplProj, blockComplProj, Matrix.diagonal_map (map_zero ι)]
  congr 1
  funext i
  split_ifs <;> simp

theorem coe_map_specialLinear (ι : K →+* F) (g : SpecialLinearGroup (Fin n) K) :
    ((SpecialLinearGroup.map ι g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) K).map ι := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem map_conj_map_blockSpecialLinear (ι : K →+* F) {I J : Finset (Fin n)}
    {g : SpecialLinearGroup (Fin n) K}
    (hg : blockComplProj J * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * blockComplProj I) :
    (blockSpecialLinear (K := F) I).map
        (MulAut.conj (SpecialLinearGroup.map ι g)).toMonoidHom =
      blockSpecialLinear J := by
  refine map_conj_blockSpecialLinear_of_mul_eq _ ?_
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.map ι) hg
  simp only [Matrix.map_mul, map_blockComplProj] at h
  rw [coe_map_specialLinear]
  exact h

@[expose] noncomputable def conjBlockEquiv (ι : K →+* F) {I J : Finset (Fin n)}
    (g : SpecialLinearGroup (Fin n) K)
    (hg : blockComplProj J * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * blockComplProj I) :
    blockSpecialLinear (K := F) I ≃* blockSpecialLinear (K := F) J :=
  ((blockSpecialLinear (K := F) I).equivMapOfInjective
      (MulAut.conj (SpecialLinearGroup.map ι g)).toMonoidHom (MulEquiv.injective _)).trans
    (MulEquiv.subgroupCongr (map_conj_map_blockSpecialLinear ι hg))

theorem coe_conjBlockEquiv_apply (ι : K →+* F) {I J : Finset (Fin n)}
    (g : SpecialLinearGroup (Fin n) K)
    (hg : blockComplProj J * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * blockComplProj I) (x : blockSpecialLinear (K := F) I) :
    ((conjBlockEquiv ι g hg x : blockSpecialLinear (K := F) J) : SpecialLinearGroup (Fin n) F) =
      SpecialLinearGroup.map ι g * x * (SpecialLinearGroup.map ι g)⁻¹ :=
  rfl

theorem coe_conjBlockEquiv_symm_apply (ι : K →+* F) {I J : Finset (Fin n)}
    (g : SpecialLinearGroup (Fin n) K)
    (hg : blockComplProj J * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * blockComplProj I) (y : blockSpecialLinear (K := F) J) :
    (((conjBlockEquiv ι g hg).symm y : blockSpecialLinear (K := F) I) :
        SpecialLinearGroup (Fin n) F) =
      (SpecialLinearGroup.map ι g)⁻¹ * y * SpecialLinearGroup.map ι g := by
  have h := congrArg (fun z : blockSpecialLinear (K := F) J => (z : SpecialLinearGroup (Fin n) F))
    (MulEquiv.apply_symm_apply (conjBlockEquiv ι g hg) y)
  simp only [coe_conjBlockEquiv_apply] at h
  rw [← h]
  group

end Blocks

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type*}
  [Field F] {e : L ≃* LinearFlag.projectiveSL n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {X : Subgroup G} {N : Finset (Fin n)}

theorem map_map_specialLinear_eq (hσι : ∀ c : K, σ (ι c) = ι c)
    (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.map σ.toRingHom (SpecialLinearGroup.map ι g) =
      SpecialLinearGroup.map ι g := by
  ext i j
  simp [SpecialLinearGroup.map_apply_coe, hσι]

theorem FieldNeighbourParam.conj [Finite G] (P : FieldNeighbourParam e t ι σ X N)
    (htC : t ∈ centralizer (L : Set G)) (hσι : ∀ c : K, σ (ι c) = ι c)
    {ρ : Equiv.Perm (Fin n)} {g : SpecialLinearGroup (Fin n) K}
    (hgd : ∀ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) * diagonal d =
      diagonal (d ∘ ρ.symm) * (g : Matrix (Fin n) (Fin n) K))
    (hgP : blockComplProj (N.map ρ.toEmbedding) * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * blockComplProj N) :
    Nonempty (FieldNeighbourParam e t ι σ
      (X.map (MulAut.conj ((e.symm (LinearFlag.proj n K g) : L) : G)).toMonoidHom)
      (N.map ρ.toEmbedding)) := by
  set w : G := ((e.symm (LinearFlag.proj n K g) : L) : G) with hw
  set γ := (conjBlockEquiv (F := F) ι g hgP).symm with hγ
  have hγapp : ∀ y, ((γ y : blockSpecialLinear (K := F) N) : SpecialLinearGroup (Fin n) F) =
      (SpecialLinearGroup.map ι g)⁻¹ * y * SpecialLinearGroup.map ι g :=
    coe_conjBlockEquiv_symm_apply ι g hgP
  let Φ' : blockSpecialLinear (K := F) (N.map ρ.toEmbedding) →* G :=
    (MulAut.conj w).toMonoidHom.comp (P.Φ.comp γ.toMonoidHom)
  have hΦ' : ∀ y, Φ' y = w * P.Φ (γ y) * w⁻¹ := fun y => rfl
  have hconj : ∀ y : SpecialLinearGroup (Fin n) K,
      w * ((e.symm (LinearFlag.proj n K y) : L) : G) * w⁻¹ =
        ((e.symm (LinearFlag.proj n K (g * y * g⁻¹)) : L) : G) := fun y => by
    simp only [hw, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨⟨Φ', ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    have hγs : (P.Φ.comp γ.toMonoidHom).range = P.Φ.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective γ),
        ← MonoidHom.range_eq_map]
    rw [MonoidHom.range_comp, hγs, P.range_eq, map_centralizerPerfectCore]
  ·
    intro y hy
    have h1 : P.Φ (γ y) = 1 := (MulEquiv.map_eq_one_iff (MulAut.conj w)).1 hy
    have hz := P.ker_le h1
    rw [mem_center_iff] at hz ⊢
    intro z
    apply γ.injective
    rw [map_mul, map_mul, hz (γ z)]
  ·
    intro x
    have hy : g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g ∈ blockSpecialLinear (K := K) N := by
      have hx : (x : SpecialLinearGroup (Fin n) K) ∈
          (blockSpecialLinear (K := K) N).map (MulAut.conj g).toMonoidHom := by
        rw [map_conj_blockSpecialLinear_of_mul_eq g hgP]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g = y := by
        rw [← hyx]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this]
      exact hy
    have hγx : γ ⟨SpecialLinearGroup.map ι x, map_ringHom_mem_blockSpecialLinear ι x.2⟩ =
        ⟨SpecialLinearGroup.map ι (g⁻¹ * x * g), map_ringHom_mem_blockSpecialLinear ι hy⟩ := by
      apply Subtype.ext
      rw [hγapp]
      simp only [map_mul, map_inv]
    rw [hΦ', hγx, P.N1 ⟨_, hy⟩, hconj]
    congr 3
    group
  ·
    intro c y
    set c' : blockTorusParam (K := K) (∅ : Finset (Fin n)) := permParam ρ.symm c with hc'
    have hcc : permParam ρ c' = c := Subtype.ext (by
      funext i
      simp [hc', coe_permParam])
    have hd : g * torusDiagSL c' * g⁻¹ = torusDiagSL c := by
      rw [conj_torusDiagSL_of_monomial hgd c', hcc]
    have hd' : torusDiagSL c' = g⁻¹ * torusDiagSL c * g := by
      rw [← hd]
      group
    have hγc : γ (conjDiag ι (N.map ρ.toEmbedding) c y) = conjDiag ι N c' (γ y) := by
      apply Subtype.ext
      rw [hγapp, coe_conjDiag_apply, coe_conjDiag_apply, hγapp, hd']
      simp only [map_mul, map_inv]
      group
    have hw' : w * ((e.symm (LinearFlag.proj n K (torusDiagSL c')) : L) : G) * w⁻¹ =
        ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) := by
      rw [hconj, hd]
    rw [hΦ', hΦ', hγc, P.N2 c' (γ y), ← hw']
    group
  ·
    intro y
    have htw : t * w = w * t := (mem_centralizer_iff.1 htC w (e.symm _).2).symm
    have hσγ : mapBlock σ N (γ y) = γ (mapBlock σ (N.map ρ.toEmbedding) y) := by
      apply Subtype.ext
      rw [coe_mapBlock_apply, hγapp, hγapp, coe_mapBlock_apply]
      simp only [map_mul, map_inv, map_map_specialLinear_eq hσι]
    rw [hΦ', hΦ', ← hσγ, ← P.N3 (γ y)]
    calc t * (w * P.Φ (γ y) * w⁻¹) * t⁻¹ = (t * w) * P.Φ (γ y) * (t * w)⁻¹ := by group
      _ = (w * t) * P.Φ (γ y) * (w * t)⁻¹ := by rw [htw]
      _ = w * (t * P.Φ (γ y) * t⁻¹) * w⁻¹ := by group

theorem nonempty_fieldNeighbourParam_rootTorus_of_nonempty [Finite G]
    (htC : t ∈ centralizer (L : Set G)) (hσι : ∀ c : K, σ (ι c) = ι c) {a b : Fin n}
    (hab : a ≠ b)
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
      (({a, b} : Finset (Fin n))ᶜ)))
    {a' b' : Fin n} (hab' : a' ≠ b') :
    Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab'))
      (({a', b'} : Finset (Fin n))ᶜ)) := by
  obtain ⟨P⟩ := hP
  obtain ⟨ρ, rfl, rfl⟩ := exists_perm_apply_eq_apply_eq hab hab'
  obtain ⟨g, hgd, hgP⟩ := exists_monomial (K := K) ρ
  have h := P.conj htC hσι hgd (hgP _)
  have hX : (modelToG e (rootTorus (K := K) hab)).map
      (MulAut.conj ((e.symm (LinearFlag.proj n K g) : L) : G)).toMonoidHom =
        modelToG e (rootTorus (K := K) hab') := by
    rw [← modelToG_map_conj, map_conj_rootTorus_of_monomial hgd hab]
  have hN : (({a, b} : Finset (Fin n))ᶜ).map ρ.toEmbedding = ({ρ a, ρ b} : Finset (Fin n))ᶜ :=
    (Neighbour.index_map ρ (.root a b hab)).symm
  rw [hX, hN] at h
  exact h

theorem nonempty_fieldNeighbourParam_levTorus_of_nonempty [Finite G]
    (htC : t ∈ centralizer (L : Set G)) (hσι : ∀ c : K, σ (ι c) = ι c) {a : Fin n}
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ)))
    (a' : Fin n) :
    Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a')) ({a'}ᶜ)) := by
  obtain ⟨P⟩ := hP
  obtain ⟨ρ, rfl⟩ : ∃ ρ : Equiv.Perm (Fin n), ρ a = a' :=
    ⟨Equiv.swap a a', Equiv.swap_apply_left a a'⟩
  obtain ⟨g, hgd, hgP⟩ := exists_monomial (K := K) ρ
  have h := P.conj htC hσι hgd (hgP _)
  have hX : (modelToG e (levTorus (K := K) a)).map
      (MulAut.conj ((e.symm (LinearFlag.proj n K g) : L) : G)).toMonoidHom =
        modelToG e (levTorus (K := K) (ρ a)) := by
    rw [← modelToG_map_conj, map_conj_levTorus_of_monomial hgd a]
  have hN : (({a} : Finset (Fin n))ᶜ).map ρ.toEmbedding = ({ρ a} : Finset (Fin n))ᶜ :=
    (Neighbour.index_map ρ (.levi a)).symm
  rw [hX, hN] at h
  exact h

end Transport

section Comm

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

theorem pieceCore_le_centralizer_map_perm (e : L ≃* LinearFlag.projectiveSL n K)
    {I J : Finset (Fin n)} (h : pieceCore e I ≤ centralizer (pieceCore e J : Set G))
    (ρ : Equiv.Perm (Fin n)) :
    pieceCore e (I.map ρ.toEmbedding) ≤
      centralizer (pieceCore e (J.map ρ.toEmbedding) : Set G) := by
  obtain ⟨w, -, hw, -⟩ := exists_pieceCore_map_conj e ρ
  rw [(hw I).1, (hw J).1]
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hxy := mem_centralizer_iff.1 (h hx) y hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc w * y * w⁻¹ * (w * x * w⁻¹) = w * (y * x) * w⁻¹ := by group
    _ = w * (x * y) * w⁻¹ := by rw [hxy]
    _ = w * x * w⁻¹ * (w * y * w⁻¹) := by group

theorem pieceCore_pair_le_centralizer_of_injective (e : L ≃* LinearFlag.projectiveSL n K)
    {a b c d : Fin n} (hinj : Function.Injective ![a, b, c, d])
    (h : pieceCore e ({a, b} : Finset (Fin n)) ≤
      centralizer (pieceCore e ({c, d} : Finset (Fin n)) : Set G))
    {a' b' c' d' : Fin n} (hinj' : Function.Injective ![a', b', c', d']) :
    pieceCore e ({a', b'} : Finset (Fin n)) ≤
      centralizer (pieceCore e ({c', d'} : Finset (Fin n)) : Set G) := by
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair _ _ hinj hinj'
  have h0 : ρ a = a' := by simpa using hρ 0
  have h1 : ρ b = b' := by simpa using hρ 1
  have h2 : ρ c = c' := by simpa using hρ 2
  have h3 : ρ d = d' := by simpa using hρ 3
  have hab : ({a, b} : Finset (Fin n)).map ρ.toEmbedding = {a', b'} := by
    rw [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding, h0, h1]
  have hcd : ({c, d} : Finset (Fin n)).map ρ.toEmbedding = {c', d'} := by
    rw [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding, h2, h3]
  have := pieceCore_le_centralizer_map_perm e h ρ
  rwa [hab, hcd] at this

theorem injective_nodePair_nodePair {m : ℕ} (i j : Fin m) (hij : (i : ℕ) + 1 < j) :
    Function.Injective ![i.castSucc, i.succ, j.castSucc, j.succ] := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    simp_all [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] <;> omega

theorem forall_pieceCore_nodePair_le_centralizer {m : ℕ}
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {a b c d : Fin (m + 1)}
    (hinj : Function.Injective ![a, b, c, d])
    (h : pieceCore e ({a, b} : Finset (Fin (m + 1))) ≤
      centralizer (pieceCore e ({c, d} : Finset (Fin (m + 1))) : Set G)) :
    ∀ i j : Fin m, (i : ℕ) + 1 < j →
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤
        centralizer (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) : Set G) :=
  fun i j hij => pieceCore_pair_le_centralizer_of_injective e hinj h
    (injective_nodePair_nodePair i j hij)

end Comm

end CFSG.SeitzReduction.LinearPilot

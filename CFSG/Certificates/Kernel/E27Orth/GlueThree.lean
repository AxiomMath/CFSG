module

public import CFSG.Certificates.Kernel.E27Orth.F3Sound
public import CFSG.Certificates.Kernel.J4Hub.FlagSound
public import CFSG.HardMathSupport.Foote.E27.LieThree.OrthThreeOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.KD.E27Orth

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub Subgroup Matrix
open CFSG.RankThree.PartOne.N143.O7

@[expose] noncomputable def eO : Idx ≃ Fin 7 :=
  Equiv.ofBijective
    (fun a => match a with
      | .inl i => ⟨6 - i.val, by omega⟩
      | .inr (.inl i) => ⟨i.val, by have := i.isLt; omega⟩
      | .inr (.inr _) => ⟨3, by omega⟩) (by decide)

@[expose] def gr7 : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  Matrix.of fun i j => if i.val + j.val = 6 then (if i.val = 3 then 2 else 1) else 0

theorem gramM_eq : gramM = gr7.submatrix eO eO := by decide +kernel

@[expose] noncomputable def matO7 : ↥Om →* Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  (Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) eO).toMonoidHom.comp
    ((Units.coeHom _).comp Om.subtype)

theorem matO7_injective : Function.Injective matO7 := by
  intro x y h
  have h1 := (Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) eO).injective h
  exact Subtype.ext (Units.ext h1)

@[expose] noncomputable def glGram7 (A : Matrix Idx Idx (ZMod 3)) (h : Aᵀ * gramM * A = gramM) :
    GL Idx (ZMod 3) :=
  have h1 : gramM * Aᵀ * gramM * A = 1 := by
    rw [Matrix.mul_assoc (gramM * Aᵀ), Matrix.mul_assoc gramM, ← Matrix.mul_assoc Aᵀ, h,
      CFSG.HardMathSupport.Foote.E27.gramM_mul_self]
  ⟨A, gramM * Aᵀ * gramM, mul_eq_one_comm.1 h1, h1⟩

theorem gram_sub {X : Matrix (Fin 7) (Fin 7) (ZMod 3)} (h : Xᵀ * gr7 * X = gr7) :
    (X.submatrix eO eO)ᵀ * gramM * X.submatrix eO eO = gramM := by
  rw [gramM_eq, transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, h]

theorem gen_om {M Y : Matrix (Fin 7) (Fin 7) (ZMod 3)} (hM : Mᵀ * gr7 * M = gr7)
    (hY : Yᵀ * gr7 * Y = gr7) (hi : Y * M = M * M * Y) : ∃ g : ↥Om, matO7 g = M := by
  have hmem : glGram7 _ (gram_sub hM) ∈ Om := by
    refine mem_om_of_inverted (h := glGram7 _ (gram_sub hY))
      (mem_iso_of_gram (A := glGram7 _ (gram_sub hM)) (gram_sub hM))
      (mem_iso_of_gram (A := glGram7 _ (gram_sub hY)) (gram_sub hY)) (Units.ext ?_)
    change Y.submatrix eO eO * M.submatrix eO eO =
      M.submatrix eO eO * M.submatrix eO eO * Y.submatrix eO eO
    rw [submatrix_mul_equiv, submatrix_mul_equiv, submatrix_mul_equiv, hi]
  refine ⟨⟨_, hmem⟩, ?_⟩
  change Matrix.reindex eO eO (M.submatrix eO eO) = M
  rw [Matrix.reindex_apply, submatrix_submatrix]
  simp

theorem card_le_of_lowerUni {m : ℕ} {g : ℕ → ↥Om} (hlu : ∀ j < m, LowerUni (matO7 (g j))) :
    Nat.card (gS m g) ≤ 3 ^ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ : ↥Om →* GL (Fin 7) (ZMod 3) :=
    (Units.map (Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) eO).toMonoidHom).comp Om.subtype
  have hψ : ∀ x, ((ψ x : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) = matO7 x :=
    fun _ => rfl
  have hle : gS m g ≤ (luSub 3 7).comap ψ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    change LowerUni ((ψ (g j) : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3))
    rw [hψ]
    exact hlu j hj
  have hpg : IsPGroup 3 (gS m g) := by
    intro x
    refine ⟨7, Subtype.ext (matO7_injective ?_)⟩
    have hU : LowerUni ((ψ x : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) := hle x.2
    rw [hψ] at hU
    rw [Subgroup.coe_pow, map_pow, hU.pow_eq_one, OneMemClass.coe_one, map_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  have hdvd : 3 ^ k ∣ Nat.card ↥Om := hk ▸ Subgroup.card_subgroup_dvd_card _
  have hk9 : k ≤ 9 :=
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1 hdvd).trans
      CFSG.HardMathSupport.Foote.E27.factorization_three_om_le
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk9

theorem syl_glue {L H CM RM ONE LV HV nR : ℕ} {G Y E Tr Ss W Rp Cm : ℕ → ℕ}
    (hc : constsOK 3 6 42 7 3 L H CM RM ONE LV HV = true)
    (hgram : ∀ j : Fin 3, (ordMat 3 7 6 42 (G j))ᵀ * gr7 * ordMat 3 7 6 42 (G j) = gr7)
    (hgramY : ∀ j : Fin 3, (ordMat 3 7 6 42 (Y j))ᵀ * gr7 * ordMat 3 7 6 42 (Y j) = gr7)
    (hinv : ∀ j : Fin 3, ordMat 3 7 6 42 (Y j) * ordMat 3 7 6 42 (G j) =
      ordMat 3 7 6 42 (G j) * ordMat 3 7 6 42 (G j) * ordMat 3 7 6 42 (Y j))
    (hlu : ∀ j : Fin 3,
      Matrix.of (fun a b : Fin 7 => if a ≤ b then ordMat 3 7 6 42 (G j) a b else 0) = 1)
    (hbase : baseI (validM 3 294 L H) ONE 3 G = true)
    (htree : ∀ i < 19683, treeI (mulR 3 6 42 7 3 L H CM RM) (validM 3 294 L H) ONE 3 G E Tr i = true)
    (hkey : ∀ k < 19683, keyI 19683 E Ss k = true)
    (hconj : ∀ i < 19683, conjI (mulR 3 6 42 7 3 L H CM RM) 19683 nR E Rp W i = true)
    (hrep : ∀ r < nR,
      repI (mulR 3 6 42 7 3 L H CM RM) (validM 3 294 L H) ONE 19683 81 E Rp Cm r = true) :
    ∃ S : Subgroup ↥Om, Nat.card S = 3 ^ 9 ∧
      ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ centralizer ({s} : Set ↥Om)) := by
  have henc := encLane hc (nb := 294) rfl
  obtain ⟨hcone, hone⟩ := oneLane hc (nb := 294) rfl
  have hex : ∀ j < 3, ∃ x : ↥Om, matO7 x = ordMat 3 7 6 42 (G j) := fun j hj =>
    gen_om (hgram ⟨j, hj⟩) (hgramY ⟨j, hj⟩) (hinv ⟨j, hj⟩)
  classical
  let g : ℕ → ↥Om := fun j => if h : j < 3 then (hex j h).choose else 1
  have hg : ∀ j < 3, matO7 (g j) = ordMat 3 7 6 42 (G j) := by
    intro j hj
    simp only [g, dif_pos hj]
    exact (hex j hj).choose_spec
  have hle : Nat.card (gS 3 g) ≤ 19683 := by
    refine (card_le_of_lowerUni (m := 3) fun j hj => ?_).trans (by norm_num)
    rw [hg j hj]
    have e : ∀ a b : Fin 7, a ≤ b → ordMat 3 7 6 42 (G j) a b = (1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) a b := by
      intro a b hab
      have := congrFun (congrFun (hlu ⟨j, hj⟩) a) b
      rwa [Matrix.of_apply, if_pos hab] at this
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [e a b hab.le, Matrix.one_apply_ne (ne_of_lt hab)]
    · rw [e a a le_rfl, Matrix.one_apply_eq]
  obtain ⟨X, hX, hinj⟩ := tab_tree henc matO7_injective hone hg hbase htree hkey
  have hsurj := tab_bound hle (fun i hi => (hX i hi).1) hinj
  have hcard : Nat.card (gS 3 g) = 3 ^ 9 :=
    (card_of_tab (fun i hi => (hX i hi).1) hinj hsurj).trans (by norm_num)
  refine ⟨gS 3 g, hcard, fun s hs h3 => ?_⟩
  have hs3 := pow_orderOf_eq_one s
  rw [h3] at hs3
  have h81 := kill_sound henc matO7_injective hone hcone
    (fun i hi => (treeI_spec (htree i hi)).1) hX hinj hsurj hconj hrep s hs hs3
  exact dvd81_of_le hcard inf_le_left h81

theorem all_of_blocks {f : ℕ → Bool} {c m : ℕ}
    (h : ∀ k < m, allN c (fun i => f (Nat.add (Nat.mul c k) i)) = true) :
    ∀ i < c * m, f i = true := by
  intro i hi
  have hc : 0 < c := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
  have := CFSG.KS.allN_spec (h (i / c) (Nat.div_lt_of_lt_mul hi)) (i % c) (Nat.mod_lt _ hc)
  rwa [Nat.add_eq, Nat.mul_eq, Nat.div_add_mod] at this

end CFSG.KD.E27Orth

end

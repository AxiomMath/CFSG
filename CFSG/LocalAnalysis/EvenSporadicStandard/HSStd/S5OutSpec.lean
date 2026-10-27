module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CntSpec
public import CFSG.Permutation.SymmetricCoxeter
public import Certificates.Certificate26961

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Permutation.SymmetricCoxeter

theorem mem_closure_of_any_eqA {gs : Array (Array ℕ)} {c : ArrCert}
    (hmem : ∀ x, x ∈ Subgroup.closure (permsA 100 gs) ↔
      ∃ i < c.pts.size, permOfArr 100 c.pts[i]! = x)
    (hval : ∀ i < c.pts.size, validA 100 c.pts[i]! = true) {a : Array ℕ}
    (ha : validA 100 a = true) (hany : c.pts.toList.any (eqA 100 a) = true) :
    permOfArr 100 a ∈ Subgroup.closure (permsA 100 gs) := by
  obtain ⟨x, hx, hxe⟩ := List.any_eq_true.1 hany
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hx)
  have hi' : c.pts[i]! = c.pts[i] := getElem!_pos c.pts i hi
  have hr := rep_of_validA (hval i hi)
  rw [← hi'] at hxe
  have := (eqA_iff (rep_of_validA ha) hr).1 hxe
  exact (hmem _).2 ⟨i, hi, this.symm⟩

theorem isSwap_adjSwap {i : ℕ} (hi : i < 7) : (adjSwap 7 i).IsSwap := by
  rw [adjSwap_of_lt hi]
  exact ⟨_, _, by simp [Fin.ext_iff], rfl⟩

theorem sign_adjSwap {i : ℕ} (hi : i < 7) : Equiv.Perm.sign (adjSwap 7 i) = -1 := by
  rw [adjSwap_of_lt hi, Equiv.Perm.sign_swap]
  simp [Fin.ext_iff]

@[expose] noncomputable def s5oS1 : Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure (permsA 100 s5oSGens)

@[expose] noncomputable def s5oz : Equiv.Perm (Fin 100) := permOfArr 100 s5oZ

@[expose] noncomputable def s5oy : Equiv.Perm (Fin 100) := permOfArr 100 s5oY

@[expose] noncomputable def s5os : Equiv.Perm (Fin 100) := permOfArr 100 s5oS

@[expose] noncomputable def s5ox (i : ℕ) : Equiv.Perm (Fin 100) := permOfArr 100 s5oXs[i]!

theorem s5o_spec1 :
    s5oS1 ≤ hs100R ∧ Nat.card s5oS1 = 1024 ∧ s5oz ∈ hs100P ∧ s5oz * s5oz = 1 ∧ s5oz ≠ 1 ∧
      (∀ x ∈ s5oS1, x ∈ hs100P → s5oz * x = x * s5oz) ∧ s5oy ∈ s5oS1 ∧ s5oy ∉ hs100P ∧
      s5oy * s5oy = 1 ∧ s5os ∈ s5oS1 ∧ s5os * s5oy * s5os⁻¹ = s5oy * s5oz ∧
      s5oz * s5oy = s5oy * s5oz ∧
      ∃ ψ : Equiv.Perm (Fin 8) →* Equiv.Perm (Fin 100), Function.Injective ψ ∧
        ψ.range = centralizer ({s5oy} : Set (Equiv.Perm (Fin 100))) ⊓ hs100P ∧
        (∃ σ₀ ∈ alternatingGroup (Fin 8), ψ σ₀ = s5oz) ∧
        (∃ κ ∉ alternatingGroup (Fin 8), ψ κ * s5oz = s5oz * ψ κ) ∧
        (∀ σ, ψ σ * s5oz = s5oz * ψ σ → ψ σ ^ 5 = 1 → ψ σ = 1) ∧
        (∀ i < 6, s5ox i * s5ox (i + 1) ∈ (alternatingGroup (Fin 8)).map ψ) := by
  classical
  have h : s5oOK = true := Certificates.certificate26961
  simp only [s5oOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨henum, hsize⟩, hsift⟩, hvz⟩, hinz⟩, hnez⟩, hz2⟩, hcen⟩, hvy⟩, hny⟩,
    hy2⟩, hyin⟩, hvs⟩, hsin⟩, hsy⟩, hxs⟩, hcox⟩, henumX⟩, hsizeX⟩, hcent⟩, hzok⟩ := h
  have hps : ∀ p ∈ s5Keys, p < 100 := by
    intro p hp
    simp only [s5Keys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps henum
  have hrz : Rep 100 s5oZ (permOfArr 100 s5oZ) := rep_of_validA hvz
  have hzP : permOfArr 100 s5oZ ∈ hs100P := (s5InP_iff hvz).1 hinz
  have hu : Rep 100 s5U hs100U := rep_hs100U
  have hry : Rep 100 s5oY (permOfArr 100 s5oY) := rep_of_validA hvy
  have hrs : Rep 100 s5oS (permOfArr 100 s5oS) := rep_of_validA hvs
  have hne1 : permOfArr 100 s5oZ ≠ 1 := by
    intro h1
    have h2 : eqA 100 s5oZ (idA 100) = true := (eqA_iff hrz rep_idA).2 h1
    rw [h2] at hnez
    exact absurd hnez (by simp)
  have hyP : permOfArr 100 s5oY ∉ hs100P := by
    intro h1
    have h2 : s5InP s5oY = true := (s5InP_iff hvy).2 h1
    rw [h2] at hny
    exact absurd hny (by simp)
  have hyy : permOfArr 100 s5oY * permOfArr 100 s5oY = 1 :=
    (eqA_iff (rep_compA hry hry) rep_idA).1 hy2
  have hsyz : permOfArr 100 s5oS * permOfArr 100 s5oY =
      permOfArr 100 s5oY * permOfArr 100 s5oZ * permOfArr 100 s5oS :=
    (eqA_iff (rep_compA hrs hry) (rep_compA (rep_compA hry hrz) hrs)).1 hsy
  set xs : ℕ → Equiv.Perm (Fin 100) := s5ox with hxsdef
  have hxsz : s5oXs.size = 7 := rfl
  have hxsv : ∀ i < 7, validA 100 s5oXs[i]! = true ∧ s5InP s5oXs[i]! = true ∧
      eqA 100 (compA 100 s5oXs[i]! s5oY) (compA 100 s5oY s5oXs[i]!) = true := by
    intro i hi
    have := allLt_spec hxs hi
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hxP : ∀ i < 7, xs i ∈ hs100P := fun i hi =>
    (s5InP_iff (hxsv i hi).1).1 (hxsv i hi).2.1
  have hxc : ∀ i < 7, xs i * permOfArr 100 s5oY = permOfArr 100 s5oY * xs i := fun i hi =>
    (eqA_iff (rep_compA (rep_of_validA (hxsv i hi).1) hry)
      (rep_compA hry (rep_of_validA (hxsv i hi).1))).1 (hxsv i hi).2.2
  have hcoxeter : IsCoxeterA 7 xs := by
    simp only [s5oCoxeterOK, Bool.and_eq_true] at hcox
    obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hcox
    have hrx : ∀ i < 7, Rep 100 s5oXs[i]! (xs i) := fun i hi =>
      rep_of_validA (hxsv i hi).1
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
    · exact (eqA_iff (rep_compA (hrx i hi) (hrx i hi)) rep_idA).1 (allLt_spec hc1 hi)
    · have hi6 : i < 6 := by omega
      exact (eqA_iff (rep_compA (rep_compA (hrx i (by omega)) (hrx (i + 1) hi)) (hrx i (by omega)))
        (rep_compA (rep_compA (hrx (i + 1) hi) (hrx i (by omega))) (hrx (i + 1) hi))).1
        (allLt_spec hc2 hi6)
    · have h1 := allLt_spec (allLt_spec hc3 (by omega : i < 7)) hj
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
      rcases h1 with h1 | h1
      · omega
      · exact (eqA_iff (rep_compA (hrx i (by omega)) (hrx j hj))
          (rep_compA (hrx j hj) (hrx i (by omega)))).1 h1
  obtain ⟨hmemX, hcardX, hvalX⟩ := enumOK_spec hps henumX
  have hpermsX : permsA 100 s5oXs = xs '' Set.Iio 7 := by
    ext g
    simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_Iio, hxsz]
    exact Iff.rfl
  have hKcard : Nat.card (Subgroup.closure (xs '' Set.Iio 7)) = 40320 := by
    rw [← hpermsX, hcardX, hsizeX]
  have hKle : Subgroup.closure (xs '' Set.Iio 7) ≤
      centralizer ({permOfArr 100 s5oY} : Set (Equiv.Perm (Fin 100))) ⊓ hs100P := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨mem_centralizer_singleton_iff.2 (hxc i hi), hxP i hi⟩
  have hCle : Nat.card ↥(centralizer ({permOfArr 100 s5oY} : Set (Equiv.Perm (Fin 100))) ⊓
      hs100P) ≤ 40320 := by
    simp only [s5oCentOK, Bool.and_eq_true, beq_iff_eq] at hcent
    obtain ⟨⟨⟨⟨hv, h0⟩, hfix⟩, hlen⟩, htail⟩ := hcent
    have hx : Rep 100 s5oY (permOfArr 100 s5oY) := rep_of_validA hv
    have hA := hs100ChainArrays
    have hF := chainCheckFacts hs100_chain_check.1
    have hQ := hs100Chain_valid
    have hbc : hs100Chain.baseCount = 5 := by
      rw [← hA.base_size]
      rfl
    have hi0 : 0 < hs100Chain.baseCount := by omega
    have hb0 : ((hs100Chain.base.get ⟨0, hi0⟩ : Fin 100) : ℕ) = 0 := by
      rw [hA.base_val]
      rfl
    have hfix0 : permOfArr 100 s5oY (hs100Chain.base.get ⟨0, hi0⟩) =
        hs100Chain.base.get ⟨0, hi0⟩ := by
      apply Fin.ext
      rw [← hx, hb0, h0]
    have h1 := card_centralizer_inf_levelSubgroup_le hA hF hQ hx hi0 hfix0
    have h2 := card_centralizer_inf_levelSubgroup_le_of_tailOK hA hF hQ hx (m := 1) (by omega)
      (E := s5oE) (by
        rw [hbc]
        exact htail)
    rw [hs100P_eq_original, ← hs100Chain.levelSubgroup_zero_eq_original hQ]
    have hcount : fixLevCount 100 (rawLevels 100 hs100StrongArrs hs100BaseArr) s5oY 0 = 30 := hfix
    rw [hcount] at h1
    calc _ ≤ 30 * Nat.card ↥(Subgroup.centralizer ({permOfArr 100 s5oY} :
          Set (Equiv.Perm (Fin 100))) ⊓ hs100Chain.levelSubgroup (0 + 1)) := h1
      _ ≤ 30 * 1344 := Nat.mul_le_mul_left _ (h2.trans hlen.le)
  have hKeq : Subgroup.closure (xs '' Set.Iio 7) =
      centralizer ({permOfArr 100 s5oY} : Set (Equiv.Perm (Fin 100))) ⊓ hs100P :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [hKcard]; exact hCle)
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 7 xs hcoxeter
  have hψrange : ψ.range = Subgroup.closure (xs '' Set.Iio 7) := by
    rw [MonoidHom.range_eq_map, ← closure_adjSwap 7, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, (hψ i hi).symm ▸ rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, hψ i hi⟩
  have hpc : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hψrange, hKcard, hpc] at h
    omega
  simp only [s5oZOK, Bool.and_eq_true, beq_iff_eq] at hzok
  obtain ⟨⟨⟨⟨⟨hzw1, hzw2⟩, hzw3⟩, hzw4⟩, hzy⟩, hzf⟩ := hzok
  have hword : ∀ i ∈ s5oZWord, i < 7 := by
    intro i hi
    have := List.all_eq_true.1 hzw1 i hi
    simpa using this
  have hzy' : permOfArr 100 s5oZ * permOfArr 100 s5oY = permOfArr 100 s5oY * permOfArr 100 s5oZ :=
    (eqA_iff (rep_compA hrz hry) (rep_compA hry hrz)).1 hzy
  have hrprod : ∀ (w : List ℕ), (∀ i ∈ w, i < 7) → ∀ (acc : Array ℕ) (g : Equiv.Perm (Fin 100)),
      Rep 100 acc g →
      Rep 100 (w.foldl (fun acc i => compA 100 acc s5oXs[i]!) acc) (g * (w.map xs).prod) := by
    intro w
    induction w with
    | nil =>
      intro _ acc g hg
      simpa using hg
    | cons a w ih =>
      intro hw acc g hg
      have ha : a < 7 := hw a (by simp)
      have h1 := ih (fun i hi => hw i (by simp [hi])) (compA 100 acc s5oXs[a]!) (g * xs a)
        (rep_compA hg (rep_of_validA (hxsv a ha).1))
      simpa [mul_assoc] using h1
  have hzprod : permOfArr 100 s5oZ = (s5oZWord.map xs).prod := by
    have h1 := hrprod s5oZWord hword (idA 100) 1 rep_idA
    have h2 : Rep 100 (s5oWordProd s5oZWord) (1 * (s5oZWord.map xs).prod) := h1
    have := (eqA_iff h2 hrz).1 hzw3
    rw [one_mul] at this
    exact this.symm
  have hψword : ψ ((s5oZWord.map (adjSwap 7)).prod) = permOfArr 100 s5oZ := by
    rw [hzprod, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    exact hψ i (hword i hi)
  have hσ₀ : (s5oZWord.map (adjSwap 7)).prod ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_prod_list_swap]
    · rw [List.length_map]
      exact Even.neg_one_pow (by decide)
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      exact isSwap_adjSwap (hword i hi)
  have hκ : adjSwap 7 1 ∉ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_adjSwap (by norm_num)]
    decide
  have hκz : ψ (adjSwap 7 1) * permOfArr 100 s5oZ = permOfArr 100 s5oZ * ψ (adjSwap 7 1) := by
    rw [hψ 1 (by norm_num)]
    exact (eqA_iff (rep_compA (rep_of_validA (hxsv 1 (by norm_num)).1) hrz)
      (rep_compA hrz (rep_of_validA (hxsv 1 (by norm_num)).1))).1 hzw4
  have hfive : ∀ σ, ψ σ * permOfArr 100 s5oZ = permOfArr 100 s5oZ * ψ σ → ψ σ ^ 5 = 1 →
      ψ σ = 1 := by
    intro σ hc h5
    have hσmem : ψ σ ∈ Subgroup.closure (permsA 100 s5oXs) := by
      rw [hpermsX, ← hψrange]
      exact ⟨σ, rfl⟩
    obtain ⟨i, hi, hiσ⟩ := (hmemX _).1 hσmem
    have hrσ := rep_of_validA (hvalX i hi)
    rw [hiσ] at hrσ
    have hmemL : s5oXCert.pts[i]! ∈ s5oXCert.pts.toList := by
      rw [getElem!_pos _ i hi]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
    have h1 := List.all_eq_true.1 hzf _ hmemL
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
    have hc' : eqA 100 (compA 100 s5oZ s5oXCert.pts[i]!) (compA 100 s5oXCert.pts[i]! s5oZ) = true :=
      (eqA_iff (rep_compA hrz hrσ) (rep_compA hrσ hrz)).2 hc.symm
    have h5' : eqA 100 (s5oPow5 s5oXCert.pts[i]!) (idA 100) = true := by
      have hr5 : Rep 100 (s5oPow5 s5oXCert.pts[i]!) (ψ σ * (ψ σ * (ψ σ * (ψ σ * ψ σ)))) :=
        rep_compA hrσ (rep_compA hrσ (rep_compA hrσ (rep_compA hrσ hrσ)))
      refine (eqA_iff hr5 rep_idA).2 ?_
      calc ψ σ * (ψ σ * (ψ σ * (ψ σ * ψ σ))) = ψ σ ^ 5 := by simp [pow_succ, mul_assoc]
        _ = 1 := h5
    rcases h1 with (h1 | h1) | h1
    · rw [hc'] at h1
      exact absurd h1 (by simp)
    · rw [h5'] at h1
      exact absurd h1 (by simp)
    · exact (eqA_iff hrσ rep_idA).1 h1
  have hprods : ∀ i < 6, xs i * xs (i + 1) ∈ (alternatingGroup (Fin 8)).map ψ := by
    intro i hi
    refine ⟨adjSwap 7 i * adjSwap 7 (i + 1), ?_, ?_⟩
    · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, map_mul, sign_adjSwap (by omega),
        sign_adjSwap (by omega)]
      decide
    · rw [map_mul, hψ i (by omega), hψ (i + 1) (by omega)]
  refine ⟨?_, hcard.trans hsize, hzP, (eqA_iff (rep_compA hrz hrz) rep_idA).1 hz2,
    hne1, ?_, mem_closure_of_any_eqA hmem hval hvy hyin, hyP, hyy,
    mem_closure_of_any_eqA hmem hval hvs hsin, ?_, hzy', ψ, hψinj, ?_,
    ⟨_, hσ₀, hψword⟩, ⟨adjSwap 7 1, hκ, hκz⟩, hfive, hprods⟩
  · rw [s5oS1, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hkv := enumOK_gens_valid henum hk
    have hrk := rep_of_validA hkv
    have hk' := allLt_spec hsift hk
    simp only [Bool.or_eq_true] at hk'
    rcases hk' with h1 | h1
    · exact hs100P_le_R ((s5InP_iff hkv).1 h1)
    · have h2 : hs100U * permOfArr 100 s5oSGens[k]! ∈ hs100P :=
        (s5InP_iff_rep (rep_compA hu hrk)).1 h1
      have h4 := hs100R.mul_mem (hs100R.inv_mem hs100U_mem_R) (hs100P_le_R h2)
      simpa using h4
  · intro x hx hxP
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    have hrx := rep_of_validA (hval i hi)
    have hxin : s5InP s5oSCert.pts[i]! = true := (s5InP_iff (hval i hi)).2 hxP
    have hmemL : s5oSCert.pts[i]! ∈ s5oSCert.pts.toList := by
      rw [getElem!_pos _ i hi]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
    have h1 := List.all_eq_true.1 hcen _ hmemL
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h1 | h1
    · rw [hxin] at h1
      exact absurd h1 (by simp)
    · exact (eqA_iff (rep_compA hrz hrx) (rep_compA hrx hrz)).1 h1
  · calc permOfArr 100 s5oS * permOfArr 100 s5oY * (permOfArr 100 s5oS)⁻¹ =
        permOfArr 100 s5oY * permOfArr 100 s5oZ * permOfArr 100 s5oS *
          (permOfArr 100 s5oS)⁻¹ := by rw [hsyz]
      _ = permOfArr 100 s5oY * permOfArr 100 s5oZ := by group
  · rw [hψrange, hKeq]
    rfl

end CFSG.EvenSporadicStandard.HSStd

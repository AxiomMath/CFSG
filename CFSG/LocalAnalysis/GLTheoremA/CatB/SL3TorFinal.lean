module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.SL3TorMat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.SL3TorIdent
public import CFSG.LocalAnalysis.GLTheoremA.CatB.SL3TorLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Open.StatedAPI

theorem mem_core_of_mem_coreOf {G : Type} [Group G] {K : Subgroup G} {p : ℕ} (t : ↥K)
    (h : (t : G) ∈ GLAPPrimeCoreOf p K) : t ∈ GLAPPrimeCore p ↥K := by
  unfold GLAPPrimeCoreOf at h
  obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.1 h
  have : y = t := Subtype.ext hyt
  rwa [this] at hy

theorem normalizer_map_mem {H G : Type} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) {T : Subgroup H} {w : H}
    (hw : w ∈ Subgroup.normalizer (T : Set H)) :
    f w ∈ Subgroup.normalizer ((T.map f : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨w * t * w⁻¹, (Subgroup.mem_normalizer_iff.1 hw t).1 ht, ?_⟩
    simp [map_mul, map_inv]
  · intro hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 hy
    have hs' : w⁻¹ * s * w ∈ T := by
      rw [Subgroup.mem_normalizer_iff] at hw
      have := (hw (w⁻¹ * s * w)).2 (by simpa [mul_assoc] using hs)
      simpa [mul_assoc] using this
    refine ⟨w⁻¹ * s * w, hs', ?_⟩
    calc f (w⁻¹ * s * w) = (f w)⁻¹ * f s * f w := by simp [map_mul, map_inv]
      _ = (f w)⁻¹ * (f w * y * (f w)⁻¹) * f w := by rw [hsy]
      _ = y := by group

theorem isElemAbelian_map_subtype {G : Type} [Group G] {K : Subgroup G} {p : ℕ}
    (W : Subgroup ↥K) (hW : IsElemAbelian p W) :
    IsElemAbelian p (W.map K.subtype) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    have := hW.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
    exact congrArg K.subtype (congrArg Subtype.val this)
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hW.2 w hw, map_one]

theorem isPGroup_subgroupOf' {F : Type} [Field F] {p : ℕ} {A S : Subgroup (GL (Fin 3) F)}
    (hA : IsPGroup p A) : IsPGroup p (A.subgroupOf S) := by
  intro x
  obtain ⟨k, hk⟩ := hA ⟨(x : S), Subgroup.mem_subgroupOf.1 x.2⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have := congrArg (fun y : A => (y : GL (Fin 3) F)) hk
  simpa using this

theorem isUTri_det {F : Type} [Field F] {A : Matrix (Fin 3) (Fin 3) F} (hA : IsUTri A) :
    A.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [(hA _ _).2 rfl]
  · intro i j hij
    exact (hA i j).1 hij

section Final


theorem sl3TorusAt_holds (G : Type) [Group G] [Finite G] : SL3TorusAt G := by
  unfold SL3TorusAt
  intro X K hK hcat hcen
  obtain ⟨F, hF, hFfin, hchar, hmod, ⟨φ⟩⟩ := pquot_sl3_iso hK hcat hcen
  have hp : Nat.Prime 3 := Nat.prime_three
  have hcardF : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hcardF
  have hω3 : ω ^ 3 = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  let core : Subgroup ↥K := GLAPPrimeCore 3 ↥K
  let π : ↥K →* ↥(StatedSL 3 F) := φ.toMonoidHom.comp (QuotientGroup.mk' core)
  have hπsurj : Function.Surjective π :=
    φ.surjective.comp (QuotientGroup.mk'_surjective core)
  have hkerπ : π.ker = core := by
    ext x
    rw [MonoidHom.mem_ker]
    show φ (QuotientGroup.mk' core x) = 1 ↔ x ∈ core
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcopy : Nat.card (GLAPPrimeCoreOf 3 K) = Nat.card core := by
    have : GLAPPrimeCoreOf 3 K = core.map K.subtype := rfl
    rw [this, Subgroup.card_map_of_injective (Subgroup.subtype_injective K)]
  have hcop : ¬ 3 ∣ Nat.card π.ker := by
    rw [hkerπ, ← hcopy]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp K)
  let E0 : Subgroup ↥(StatedSL 3 F) := (E0G (K := F) ω hω3).subgroupOf (StatedSL 3 F)
  let U : Subgroup ↥(StatedSL 3 F) := (utriG (K := F)).subgroupOf (StatedSL 3 F)
  have hE0 : IsPGroup 3 E0 := isPGroup_subgroupOf' (isPGroup_E0G hω3)
  have hE0ab : IsElemAbelian 3 E0 := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · exact Subtype.ext (Subtype.ext (E0G_comm hω3 _ _ (Subgroup.mem_subgroupOf.1 a.2)
        (Subgroup.mem_subgroupOf.1 b.2)))
    · intro x hx
      exact Subtype.ext (E0G_pow_three hω3 _ (Subgroup.mem_subgroupOf.1 hx))
  have hE0c : Nat.card E0 = 9 := by
    rw [← card_E0G hω3 hω1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E0G_le_statedSL hω3)).toEquiv
  have hU2 : IsPGroup 2 U := isPGroup_subgroupOf' (utriG_isPGroup (K := F))
  obtain ⟨u, hu, hu1, hu2⟩ := involution_mem_utriG (K := F)
  let x₀ : ↥(StatedSL 3 F) := ⟨u, mem_statedSL_of_det (isUTri_det ((mem_utriG u).1 hu))⟩
  have hx₀U : x₀ ∈ U := Subgroup.mem_subgroupOf.2 hu
  have hx₀ : x₀ ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hx₀2 : x₀ ^ 2 = 1 := Subtype.ext hu2
  have hnorm : ∀ e ∈ E0, e ∈ Subgroup.normalizer (U : Set ↥(StatedSL 3 F)) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have he' : (e : GL (Fin 3) F) ∈ E0G (K := F) ω hω3 := Subgroup.mem_subgroupOf.1 he
    have key := Subgroup.mem_normalizer_iff.1 (E0G_le_normalizer_utriG hω3 he') (h : GL (Fin 3) F)
    show (h : GL (Fin 3) F) ∈ utriG ↔ ((e * h * e⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) ∈ utriG
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact key
  obtain ⟨W, hW3, hWab, hWcard, T, hT2, hTnorm, hTnot⟩ :=
    lift_torus π hπsurj hcop E0 U hE0 hE0ab hE0c hU2 x₀ hx₀U hx₀ hx₀2 hnorm
  refine ⟨W.map K.subtype, T.map K.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact w.2
  · exact isElemAbelian_map_subtype W hWab
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective K), hWcard]
    norm_num
  · intro x hx
    obtain ⟨t, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact t.2
  · exact hT2.map K.subtype
  · intro e he
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 he
    exact normalizer_map_mem K.subtype (Subgroup.subtype_injective K) (hTnorm w hw)
  · intro hle
    apply hTnot
    intro t ht
    have h1 : (t : G) ∈ GLAPPrimeCoreOf 3 K := hle (Subgroup.mem_map_of_mem K.subtype ht)
    have h2 := mem_core_of_mem_coreOf t h1
    have h2' : t ∈ π.ker := by
      rw [hkerπ]
      exact h2
    exact h2'

end Final

end CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor

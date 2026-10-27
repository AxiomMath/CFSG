module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerCentralizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Frattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftBasic
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open scoped commutatorElement

theorem false_of_isPSolvable_surj {N S : Type} [Group N] [Group S]
    (hN : CFSG.HallHigman.IsPSolvable 3 N) (H : Subgroup N) [H.Normal] (φ : ↥H →* S)
    (hφ : Function.Surjective φ) (hS : IsSimpleGroup S) (hnc : ¬ IsMulCommutative S) [Finite S]
    (h3 : 3 ∣ Nat.card S) : False := by
  have hsimple : IsSimpleGroup (↥H ⧸ φ.ker) :=
    MulEquiv.isSimpleGroup (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hidx : φ.ker.index = Nat.card S := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  rcases hN H (Subgroup.Normal.isSubnormal inferInstance) φ.ker hsimple with h | h
  · rw [hidx] at h
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic S := isCyclic_of_prime_card (p := 3) h
    exact hnc ⟨⟨fun a b => mul_comm a b⟩⟩
  · rw [hidx] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h h3

theorem innSub_equiv {S : Type} [Group S] [IsSimpleGroup S] (hnc : ¬ IsMulCommutative S) :
    Nonempty (S ≃* ↥(innSub S)) := by
  have hc : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      refine hnc ⟨⟨fun a b => ?_⟩⟩
      have : b ∈ Subgroup.center S := by rw [h]; trivial
      exact Subgroup.mem_center_iff.mp this a
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have : a ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro b
      have := congrArg (fun f : MulAut S => f b) ha
      have h2 : a * b * a⁻¹ = b := by simpa [MulAut.conj_apply] using this
      calc b * a = a * b * a⁻¹ * a := by rw [h2]
        _ = a * b := by group
    rw [hc] at this
    exact this
  exact ⟨MonoidHom.ofInjective hinj⟩

theorem innSub_normal' (S : Type) [Group S] : (innSub S).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨a, rfl⟩ := hx
  refine ⟨g a, ?_⟩
  ext b
  simp [MulAut.conj_apply, MulAut.mul_apply]


theorem comm_mem {G : Type*} [Group G] {M : Subgroup G} {a b : G} (ha : a ∈ M) (hb : b ∈ M) :
    ⁅a, b⁆ ∈ M := by
  rw [commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)

theorem le_normalizer_commutator_left {G : Type*} [Group G] (H₁ H₂ : Subgroup G) :
    H₁ ≤ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  have key : ∀ a ∈ H₁, ∀ x ∈ ⁅H₁, H₂⁆, a * x * a⁻¹ ∈ ⁅H₁, H₂⁆ := by
    intro a ha x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a', ha', b, hb, rfl⟩ := hx
      have e : a * ⁅a', b⁆ * a⁻¹ = ⁅a * a', b⁆ * ⁅b, a⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (⁅H₁, H₂⁆).mul_mem (Subgroup.commutator_mem_commutator (H₁.mul_mem ha ha') hb)
        ((commutatorElement_inv a b ▸ (⁅H₁, H₂⁆).inv_mem
          (Subgroup.commutator_mem_commutator ha hb) : ⁅b, a⁆ ∈ ⁅H₁, H₂⁆))
    | one => simp
    | mul x y _ _ hx hy =>
      have e : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [e]; exact (⁅H₁, H₂⁆).mul_mem hx hy
    | inv x _ hx =>
      have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [e]; exact (⁅H₁, H₂⁆).inv_mem hx
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key a ha x hx, fun hx => by simpa [mul_assoc] using key a⁻¹ (H₁.inv_mem ha) _ hx⟩


theorem layer_le_commutator_thompsonJ {G : Type} [Group G] [Finite G] {M L T : Subgroup G}
    (hlay : IsRankTwoLayer M L) (hT : IsSylowTwoOf T M)
    (hN : CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.normalizer (thompsonJ T : Set G) ⊓ M)) :
    L ≤ ⁅L, thompsonJ T⁆ ⊔ GLBPrimeCore 3 M := by
  classical
  obtain ⟨hLM, hDL, hLn, hS, hnc, hty⟩ := hlay
  set D : Subgroup G := GLBPrimeCore 3 M with hD
  set J : Subgroup G := thompsonJ T with hJ
  have hTM : T ≤ M := hT.1
  have hJT : J ≤ T := CFSG.Quasithin.B6.thompsonJ_le T
  have hJM : J ≤ M := hJT.trans hTM
  haveI hLn' : (L.subgroupOf M).Normal := hLn
  haveI hSn : (starImg M L).Normal := normal_starImg hLn
  set π : ↥M →* M ⧸ D.subgroupOf M := QuotientGroup.mk' (D.subgroupOf M) with hπ
  set S : Subgroup (M ⧸ D.subgroupOf M) := starImg M L with hSdef
  have hSmem : ∀ s ∈ S, ∃ l : ↥M, (l : G) ∈ L ∧ π l = s := by
    intro s hs
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hs
    exact ⟨l, hl, rfl⟩
  let Ψ : ↥M →* MulAut ↥S := (MulAut.conjNormal : (M ⧸ D.subgroupOf M) →* MulAut ↥S).comp π
  have hΨ : ∀ (m : ↥M) (s : ↥S),
      ((Ψ m s : ↥S) : M ⧸ D.subgroupOf M) = π m * s * (π m)⁻¹ := fun m s => by
    simp [Ψ, MulAut.conjNormal_apply]
  have hDM : M ≤ Subgroup.normalizer (D : Set G) := CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M
  by_contra hnot
  have hJtriv : ∀ (j : ↥M), (j : G) ∈ J → Ψ j = 1 := by
    intro j hj
    set R : Subgroup G := ⁅L, J⁆ ⊔ D with hR
    have hcommL : ∀ l ∈ L, ∀ j ∈ J, ⁅l, j⁆ ∈ L := by
      intro l hl j hj
      have h1 : j * l⁻¹ * j⁻¹ ∈ L :=
        conj_mem_of_normal_subgroupOf hLM hLn (hJM hj) (L.inv_mem hl)
      have e : ⁅l, j⁆ = l * (j * l⁻¹ * j⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e]; exact L.mul_mem hl h1
    have hRL : R ≤ L := sup_le (Subgroup.commutator_le.2 hcommL) hDL
    have hDR : D ≤ R := le_sup_right
    have hLR : L ≤ Subgroup.normalizer (R : Set G) :=
      fun l hl => mem_normalizer_sup (le_normalizer_commutator_left L J hl) (hDM (hLM hl))
    set R' : Subgroup (M ⧸ D.subgroupOf M) := (R.subgroupOf M).map π with hR'
    have hR'S : R' ≤ S := Subgroup.map_mono (fun x hx => hRL hx)
    have hR'n : (R'.subgroupOf S).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hR'S]
      intro h k hh hk
      obtain ⟨ρ, hρ, rfl⟩ := Subgroup.mem_map.mp hh
      obtain ⟨l, hl, rfl⟩ := hSmem k hk
      refine Subgroup.mem_map.mpr ⟨l * ρ * l⁻¹, ?_, by simp⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hlρ : (l : G) * ρ * (l : G)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hLR hl) _).mp (Subgroup.mem_subgroupOf.mp hρ)
      simpa using hlρ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R'.subgroupOf S) with hbot | htop
    ·
      have hcomm : ∀ l ∈ L, ∀ j ∈ J, ⁅l, j⁆ ∈ D := by
        intro l hl j hj
        have hlM : l ∈ M := hLM hl
        have hjM' : j ∈ M := hJM hj
        have hmem : ⁅l, j⁆ ∈ R := Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hl hj)
        have hM' : (⟨⁅l, j⁆, comm_mem hlM hjM'⟩ : ↥M) ∈ R.subgroupOf M := hmem
        have h1 : (⟨π ⟨⁅l, j⁆, comm_mem hlM hjM'⟩, hR'S (Subgroup.mem_map_of_mem π hM')⟩ :
            ↥S) ∈ R'.subgroupOf S := Subgroup.mem_map_of_mem π hM'
        rw [hbot, Subgroup.mem_bot] at h1
        have h2 : π ⟨⁅l, j⁆, comm_mem hlM hjM'⟩ = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff (N := D.subgroupOf M) _).mp h2
      ext ⟨s, hs⟩
      obtain ⟨l, hl, rfl⟩ := hSmem s hs
      rw [hΨ]
      simp only [MulAut.one_apply]
      have hc : ⁅(j : G), (l : G)⁆ ∈ D := by
        rw [← commutatorElement_inv]; exact D.inv_mem (hcomm l hl j hj)
      have hjl : (j : ↥M) * l * j⁻¹ = ⟨⁅(j : G), (l : G)⁆, comm_mem j.2 l.2⟩ * l := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [← map_inv, ← map_mul, ← map_mul, hjl, map_mul]
      have : π ⟨⁅(j : G), (l : G)⁆, comm_mem j.2 l.2⟩ = 1 :=
        (QuotientGroup.eq_one_iff (N := D.subgroupOf M) _).mpr hc
      rw [this, one_mul]
    · exfalso
      apply hnot
      intro l hl
      have hlM : l ∈ M := hLM hl
      have h1 : (⟨π ⟨l, hlM⟩, ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩⟩ : ↥S) ∈
          R'.subgroupOf S := by rw [htop]; trivial
      obtain ⟨ρ, hρ, hρl⟩ := Subgroup.mem_subgroupOf.mp h1
      have h2 : (⟨l, hlM⟩ : ↥M)⁻¹ * ρ ∈ D.subgroupOf M := by
        rw [← QuotientGroup.ker_mk' (D.subgroupOf M), MonoidHom.mem_ker, map_mul, map_inv]
        have hρl' : π ρ = π ⟨l, hlM⟩ := hρl
        rw [hρl', inv_mul_cancel]
      have h3 : (ρ : G) ∈ R := Subgroup.mem_subgroupOf.mp hρ
      have h4 : (l : G)⁻¹ * ρ ∈ D := Subgroup.mem_subgroupOf.mp h2
      have : (l : G) = ρ * ((l : G)⁻¹ * ρ)⁻¹ := by group
      rw [this]
      exact R.mul_mem h3 (R.inv_mem (hDR h4))
  set Kh : Subgroup G := Ψ.ker.map M.subtype with hKh
  have hKM : Kh ≤ M := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hMK : M ≤ Subgroup.normalizer (Kh : Set G) := by
    have key : ∀ m ∈ M, ∀ x ∈ Kh, m * x * m⁻¹ ∈ Kh := by
      rintro m hm _ ⟨k, hk, rfl⟩
      refine ⟨⟨m, hm⟩ * k * ⟨m, hm⟩⁻¹, ?_, rfl⟩
      exact (MonoidHom.normal_ker Ψ).conj_mem k hk ⟨m, hm⟩
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => key m hm x hx, fun hx => by simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ hx⟩
  have hJK : J ≤ Kh := fun j hj =>
    ⟨⟨j, hJM hj⟩, (MonoidHom.mem_ker).mpr (hJtriv ⟨j, hJM hj⟩ hj), rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (T ⊓ Kh) Kh := by
    rw [CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf] at hT ⊢
    exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hT hKM hMK
  have hJeq : thompsonJ (T ⊓ Kh) = J :=
    GammaExtra.thompsonJ_eq_of_le (le_inf hJT hJK) inf_le_left
  have hFr := frattini_amb hKM hMK hTsyl
  set N : Subgroup G := Subgroup.normalizer (J : Set G) ⊓ M with hNdef
  have hNM : N ≤ M := inf_le_right
  let ΨN : ↥N →* MulAut ↥S := Ψ.comp (Subgroup.inclusion hNM)
  have hdec : ∀ x : ↥M, ∃ n : ↥N, Ψ x = ΨN n := by
    intro x
    obtain ⟨y, hy, n, ⟨hnM, hnN⟩, hxn⟩ := hFr x x.2
    obtain ⟨k, hk, rfl⟩ := hy
    have hnJ : n ∈ Subgroup.normalizer (J : Set G) := by
      have := GammaExtra.normalizer_le_normalizer_thompsonJ (T ⊓ Kh) hnN
      rwa [hJeq] at this
    refine ⟨⟨n, hnJ, hnM⟩, ?_⟩
    have hx : x = k * ⟨n, hnM⟩ := Subtype.ext hxn
    rw [hx, map_mul, (MonoidHom.mem_ker.mp hk), one_mul]
    rfl
  haveI hInnN : (innSub ↥S).Normal := innSub_normal' _
  set H : Subgroup ↥N := (innSub ↥S).comap ΨN with hH
  haveI hHn : H.Normal := hInnN.comap ΨN
  have hmemH : ∀ n : ↥N, n ∈ H ↔ ΨN n ∈ innSub ↥S := fun n => Iff.rfl
  let φ : ↥H →* ↥(innSub ↥S) :=
    ((ΨN.comp H.subtype)).codRestrict (innSub ↥S) (fun h => h.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨a, s, rfl⟩
    obtain ⟨l₀, hl₀, hl₀s⟩ := hSmem s.1 s.2
    have hΨl : Ψ l₀ = MulAut.conj s := by
      ext t
      rw [hΨ, hl₀s]
      simp [MulAut.conj_apply]
    obtain ⟨n, hn⟩ := hdec l₀
    have hnH : n ∈ H := by
      rw [hmemH, ← hn, hΨl]
      exact ⟨s, rfl⟩
    refine ⟨⟨n, hnH⟩, Subtype.ext ?_⟩
    show ΨN n = MulAut.conj s
    rw [← hn, hΨl]
  obtain ⟨e⟩ := innSub_equiv (S := ↥S) hnc
  haveI := hS
  have hSi : IsSimpleGroup ↥(innSub ↥S) := MulEquiv.isSimpleGroup e.symm
  have hnc' : ¬ IsMulCommutative ↥(innSub ↥S) := by
    intro hc
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have := hc.is_comm.comm (e a) (e b)
    simpa using congrArg e.symm this
  have h3 : 3 ∣ Nat.card ↥(innSub ↥S) := by
    rw [← Nat.card_congr e.toEquiv]
    exact three_dvd_card_of_layerType hty
  exact false_of_isPSolvable_surj hN H φ hφ hSi hnc' h3

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

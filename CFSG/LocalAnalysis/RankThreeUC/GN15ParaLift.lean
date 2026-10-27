module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.MinPar
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.CharTwoOver
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PermutableOrderThree
import CFSG.Quasithin.EmptyFaithful.S14620A

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section ThreeGroup

variable {Y : Type} [Group Y] [Finite Y]

private theorem relIndex_sup_zpowers_of_orderOf_eq_three {Rs : Subgroup Y} (hRs : IsPGroup 2 Rs)
    {c : Y} (hc3 : orderOf c = 3) (hnorm : Rs ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Y)) :
    Rs.relIndex (Rs ⊔ Subgroup.zpowers c) = 3 := by
  have h := B6.relIndex_inf_eq_relIndex_sup hnorm
  rw [CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.inf_eq_bot_of_isPGroup_two_of_card_three hRs
    ((Nat.card_zpowers c).trans hc3), Subgroup.relIndex_bot_left, Nat.card_zpowers, hc3] at h
  exact h.symm

theorem minParabolic_sup_zpowers {Rs : Subgroup Y} (hRs : IsPGroup 2 Rs) {c : Y}
    (hc3 : orderOf c = 3) (hnorm : Rs ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Y))
    (hnot : ¬ Subgroup.zpowers c ≤ Subgroup.normalizer (Rs : Set Y)) :
    MinParabolic (Rs ⊔ Subgroup.zpowers c) Rs Rs := by
  have h3 := relIndex_sup_zpowers_of_orderOf_eq_three hRs hc3 hnorm
  have hsyl : IsSylowTwoOf Rs (Rs ⊔ Subgroup.zpowers c) := by
    refine ⟨le_sup_left, hRs, ?_⟩
    show ¬ 2 ∣ Rs.relIndex (Rs ⊔ Subgroup.zpowers c)
    rw [h3]; norm_num
  have hmax : IsMaxSubgroupIn (Rs ⊔ Subgroup.zpowers c) Rs := by
    refine ⟨lt_of_le_of_ne le_sup_left fun h => ?_, fun K hRK hKH => ?_⟩
    · have : Rs.relIndex (Rs ⊔ Subgroup.zpowers c) = 1 :=
        Subgroup.relIndex_eq_one.mpr h.symm.le
      rw [h3] at this; omega
    · have hmul := Subgroup.relIndex_mul_relIndex Rs K (Rs ⊔ Subgroup.zpowers c) hRK.le hKH
      rw [h3] at hmul
      have hne : Rs.relIndex K ≠ 1 := fun h1 => by
        have := Subgroup.relIndex_eq_one.mp h1
        exact absurd hRK (not_lt_of_ge this)
      have hdvd : Rs.relIndex K ∣ 3 := ⟨K.relIndex (Rs ⊔ Subgroup.zpowers c), hmul.symm⟩
      have h33 : Rs.relIndex K = 3 :=
        (Nat.prime_three.eq_one_or_self_of_dvd _ hdvd).resolve_left hne
      rw [h33] at hmul
      have : K.relIndex (Rs ⊔ Subgroup.zpowers c) = 1 := by omega
      exact le_antisymm hKH (Subgroup.relIndex_eq_one.mp this)
  refine ⟨hsyl, fun h => hnot (le_sup_right.trans h), isUniqueMaxOver_iff.mpr ⟨hmax, le_rfl, ?_⟩⟩
  intro N hN hRN
  by_contra hne
  have hlt : Rs < N := lt_of_le_of_ne hRN (Ne.symm hne)
  exact absurd (hmax.2 N hlt hN.1.le) hN.1.ne

omit [Finite Y] in
theorem normal_zpowers_subgroupOf_sup_of_le_normalizer {Rs : Subgroup Y} {c : Y}
    (hnorm : Rs ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Y)) :
    ((Subgroup.zpowers c).subgroupOf (Rs ⊔ Subgroup.zpowers c)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
    (sup_le hnorm Subgroup.le_normalizer)

theorem zpowers_le_normalizer_iff_forall_mul_comm {Rs : Subgroup Y} (hRs : IsPGroup 2 Rs) {c : Y}
    (hc3 : orderOf c = 3) (hnorm : Rs ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Y)) :
    Subgroup.zpowers c ≤ Subgroup.normalizer (Rs : Set Y) ↔ ∀ x ∈ Rs, x * c = c * x := by
  constructor
  · intro h x hx
    have h1 : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hx) c).mp (Subgroup.mem_zpowers c)
    have h2 : c * x⁻¹ * c⁻¹ ∈ Rs :=
      (Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_zpowers c)) x⁻¹).mp (Rs.inv_mem hx)
    have h3 : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers c :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
    have h4 : x * c * x⁻¹ * c⁻¹ ∈ Rs := by
      have := Rs.mul_mem hx h2
      simpa [mul_assoc] using this
    have h5 : x * c * x⁻¹ * c⁻¹ ∈ Rs ⊓ Subgroup.zpowers c := ⟨h4, h3⟩
    rw [CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.inf_eq_bot_of_isPGroup_two_of_card_three hRs
      ((Nat.card_zpowers c).trans hc3), Subgroup.mem_bot] at h5
    exact commutatorElement_eq_one_iff_mul_comm.1 h5
  · intro hcomm y hy
    apply Subgroup.centralizer_le_normalizer
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Commute.zpow_right (hcomm b hb : Commute b c) i).eq

theorem not_zpowers_le_normalizer_of_le {Rs Bs : Subgroup Y} (hRs : IsPGroup 2 Rs) {c : Y}
    (hc3 : orderOf c = 3) (hnorm : Rs ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Y))
    (hBR : Bs ≤ Rs) (hnotB : ¬ Subgroup.zpowers c ≤ Subgroup.normalizer (Bs : Set Y)) :
    ¬ Subgroup.zpowers c ≤ Subgroup.normalizer (Rs : Set Y) := by
  intro h
  exact hnotB ((zpowers_le_normalizer_iff_forall_mul_comm (hRs.to_le hBR) hc3
    (hBR.trans hnorm)).2 fun x hx =>
      (zpowers_le_normalizer_iff_forall_mul_comm hRs hc3 hnorm).1 h x (hBR hx))

theorem isPGroup_quotient_sup_zpowers {Rs : Subgroup Y} (hRs : IsPGroup 2 Rs) {c : Y}
    (hnorm : Rs ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Y))
    [((Subgroup.zpowers c).subgroupOf (Rs ⊔ Subgroup.zpowers c)).Normal] :
    IsPGroup 2 (↥(Rs ⊔ Subgroup.zpowers c) ⧸
      (Subgroup.zpowers c).subgroupOf (Rs ⊔ Subgroup.zpowers c)) := by
  obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hRs (Subgroup.zpowers c)
  have hidx : ((Subgroup.zpowers c).subgroupOf (Rs ⊔ Subgroup.zpowers c)).index = 2 ^ n := by
    have := B6.relIndex_sup_eq_of_le_normalizer hnorm
    rw [Subgroup.relIndex] at this
    rw [this]; exact hn
  exact IsPGroup.of_card (by rw [← Subgroup.index.eq_1, hidx])

private theorem isSolvable_sup_zpowers_of_le_normalizer {Rs : Subgroup Y} (hRs : IsPGroup 2 Rs)
    {c : Y} (hnorm : Rs ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Y)) :
    Group.IsSolvable ↥(Rs ⊔ Subgroup.zpowers c) := by
  set Hs : Subgroup Y := Rs ⊔ Subgroup.zpowers c with hHs
  have hZn : ((Subgroup.zpowers c).subgroupOf Hs).Normal :=
    normal_zpowers_subgroupOf_sup_of_le_normalizer hnorm
  have hZs : Group.IsSolvable ↥((Subgroup.zpowers c).subgroupOf Hs) := by
    apply Group.isSolvable_of_comm
    rintro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    apply Subtype.ext
    apply Subtype.ext
    simp [← zpow_add, add_comm]
  have hq : Group.IsSolvable (↥Hs ⧸ (Subgroup.zpowers c).subgroupOf Hs) := by
    have := (isPGroup_quotient_sup_zpowers hRs hnorm).isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range ((Subgroup.zpowers c).subgroupOf Hs).subtype
    (QuotientGroup.mk' ((Subgroup.zpowers c).subgroupOf Hs)) fun x hx => by
      simpa using hx

end ThreeGroup

section Lift

variable {X : Type} [Group X] [Finite X]

variable {T : Subgroup X}

theorem exists_solvable_minParabolic_lift (hX : GNSetting X T) {R : Subgroup X} (hRT : R ≤ T)
    (hCR : T ⊓ gnC T ≤ R) (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    {c : X ⧸ gnC T} (hc3 : orderOf c = 3)
    (hnorm : gnImg T R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (X ⧸ gnC T)))
    (hnot : ¬ Subgroup.zpowers c ≤ Subgroup.normalizer (gnImg T R : Set (X ⧸ gnC T))) :
    ∃ K M : Subgroup X, MinParabolic K R M ∧ CharTwo K ∧ R ≤ K ∧ Group.IsSolvable ↥K ∧
      K.map (QuotientGroup.mk' (gnC T)) = gnImg T R ⊔ Subgroup.zpowers c := by
  set π := QuotientGroup.mk' (gnC T) with hπ
  set Rs : Subgroup (X ⧸ gnC T) := gnImg T R with hRs
  set Hs : Subgroup (X ⧸ gnC T) := Rs ⊔ Subgroup.zpowers c with hHs
  have hRp : IsPGroup 2 R := hX.sylow.2.1.to_le hRT
  have hRsp : IsPGroup 2 Rs := hRp.map π
  have hmin : MinParabolic Hs Rs Rs := minParabolic_sup_zpowers hRsp hc3 hnorm hnot
  have hsolvHs : Group.IsSolvable ↥Hs := isSolvable_sup_zpowers_of_le_normalizer hRsp hnorm
  set H₀ : Subgroup X := Hs.comap π with hH₀
  have hRH₀ : R ≤ H₀ := fun r hr => (le_sup_left : Rs ≤ Hs) ⟨r, hr, rfl⟩
  have hmapH₀ : H₀.map π = Hs :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hker : π.ker = gnC T := QuotientGroup.ker_mk' _
  have hCH : gnC T ≤ H₀ := fun x hx => by
    show π x ∈ Hs
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact Hs.one_mem
  have hCn : (⊤ : Subgroup X) ≤ Subgroup.normalizer (gnC T : Set X) := fun x _ =>
    (Subgroup.normalizer_eq_top_iff.mpr (gnC_normal T)).symm ▸ Subgroup.mem_top x
  have hCsyl : IsSylowTwoOf (T ⊓ gnC T) (gnC T) :=
    B6.isSylowTwoOf_inf_normal hX.sylow le_top hCn
  have hRC : R ⊓ gnC T = T ⊓ gnC T :=
    le_antisymm (inf_le_inf_right _ hRT) (le_inf hCR inf_le_right)
  have hK : IsSylowTwoOf (R ⊓ π.ker) (H₀ ⊓ π.ker) := by
    rw [hker, hRC, inf_eq_right.mpr hCH]
    exact hCsyl
  have hSyl : IsSylowTwoOf R H₀ :=
    CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_map_ker π hRH₀ hRp hK
      (hmapH₀ ▸ hmin.isSylow)
  set N₀ : Subgroup X :=
    H₀ ⊓ Subgroup.normalizer ((T ⊓ gnC T : Subgroup X) : Set X) with hN₀
  have hfr : H₀ ≤ gnC T ⊔ N₀ :=
    B6.frattini_two hCH (fun x _ => (Subgroup.normalizer_eq_top_iff.mpr (gnC_normal T)).symm ▸
      Subgroup.mem_top x) hCsyl
  have hTn : T ≤ Subgroup.normalizer ((T ⊓ gnC T : Subgroup X) : Set X) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht,
      (Subgroup.normalizer_eq_top_iff.mpr (gnC_normal T)).symm ▸ Subgroup.mem_top t⟩
  have hRN₀ : R ≤ N₀ := le_inf hRH₀ (hRT.trans hTn)
  have hN₀H₀ : N₀ ≤ H₀ := inf_le_left
  have hmapN₀ : N₀.map π = Hs := by
    refine le_antisymm ((Subgroup.map_mono hN₀H₀).trans hmapH₀.le) ?_
    rw [← hmapH₀]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hfr hx)
    refine ⟨n, hn, ?_⟩
    rw [map_mul, show π k = 1 from (QuotientGroup.eq_one_iff k).2 hk, one_mul]
  have hNCsolv : Group.IsSolvable
      ↥(gnC T ⊓ Subgroup.normalizer ((T ⊓ gnC T : Subgroup X) : Set X)) :=
    CFSG.Quasithin.isSolvable_inf_normalizer_of_isSylowTwoOf hCsyl
  have hNCN₀ : gnC T ⊓ Subgroup.normalizer ((T ⊓ gnC T : Subgroup X) : Set X) ≤ N₀ :=
    le_inf (inf_le_left.trans hCH) inf_le_right
  have hsolvN₀ : Group.IsSolvable ↥N₀ := by
    have := hNCsolv
    have := hsolvHs
    let g : ↥N₀ →* ↥Hs := (π.comp N₀.subtype).codRestrict Hs (fun x => by
      have : (x : X) ∈ H₀ := hN₀H₀ x.2
      exact this)
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNCN₀) g fun x hx => ?_
    have hx1 : π (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxC : (x : X) ∈ gnC T := (QuotientGroup.eq_one_iff _).1 hx1
    exact ⟨⟨(x : X), hxC, x.2.2⟩, rfl⟩
  have hSylN₀ : IsSylowTwoOf R N₀ := B6.isSylowTwoOf_mono hSyl hRN₀ hN₀H₀
  obtain ⟨H₁, M₁, hRH₁, hH₁N₀, hmap, hmin₁⟩ :=
    exists_minParabolic_of_map_minParabolic (gnC T) hSylN₀ (by rw [hmapN₀]; exact hmin)
  refine ⟨H₁, M₁, hmin₁,
    CFSG.AGLEmbeddingD2.Tits.GN516.charTwo_of_pCoreOf_le hX (hQR.trans hRH₁), hRH₁, ?_,
    hmap.trans hmapN₀⟩
  have := hsolvN₀
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hH₁N₀)

end Lift

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

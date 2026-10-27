module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8Two
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4All
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Base
public import Certificates.Certificate55115

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.EvenSmallLie.OmegaEight

namespace E4O8

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C


theorem three_parts : edgeCheck L0P u0 v0 (rootP.getD 6 1) = true ∧
    norms L0P u0 v0 ((rootP.getD 0 1)⁻¹ * rootP.getD 6 1) = false ∧
    norms L0P u0 v0 ((rootP.getD 4 1)⁻¹ * rootP.getD 6 1) = false := by
  have h : threeCheck () = true := Certificates.certificate55115
  unfold threeCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have r0 := rep_getD forall₂_root 0
  have r4 := rep_getD forall₂_root 4
  have r6 := rep_getD forall₂_root 6
  refine ⟨?_, ?_, ?_⟩
  · rwa [edgeCheckA_eq forall₂_L0 u0_spec.1 v0_spec.1 r6] at h1
  · rwa [normsA_eq forall₂_L0 u0_spec.1 v0_spec.1 (rep_compA (rep_inv r0) r6)] at h2
  · rwa [normsA_eq forall₂_L0 u0_spec.1 v0_spec.1 (rep_compA (rep_inv r4) r6)] at h3

theorem three_nbrs : conjSub (rootP.getD 6 1) K0 ≠ K0 ∧
    conjSub (rootP.getD 6 1) K0 ≤ Subgroup.normalizer (K0 : Set _) ∧
    conjSub (rootP.getD 0 1) K0 ≠ conjSub (rootP.getD 6 1) K0 ∧
    conjSub (rootP.getD 4 1) K0 ≠ conjSub (rootP.getD 6 1) K0 := by
  obtain ⟨h1, h2, h3⟩ := three_parts
  obtain ⟨a1, a2⟩ := edge_of_edgeCheck mem_K0_iff h1
  refine ⟨a1, a2, fun e => ?_, fun e => ?_⟩
  · have he : conjSub ((rootP.getD 0 1)⁻¹ * rootP.getD 6 1) K0 = K0 := by
      rw [conjSub_mul, ← e, conjSub_inv_conjSub]
    rw [norms_of_conjSub_eq mem_K0_iff he] at h2
    exact Bool.noConfusion h2
  · have he : conjSub ((rootP.getD 4 1)⁻¹ * rootP.getD 6 1) K0 = K0 := by
      rw [conjSub_mul, ← e, conjSub_inv_conjSub]
    rw [norms_of_conjSub_eq mem_K0_iff he] at h3
    exact Bool.noConfusion h3

end E4O8

namespace E4Cover

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]

omit [Finite X] in
theorem exists_mem_of_mk_mem_centralizer {u m : X}
    (hc : QuotientGroup.mk' N m ∈
      Subgroup.centralizer ({QuotientGroup.mk' N u} : Set (X ⧸ N))) :
    ∃ ν ∈ N, m * u * m⁻¹ = u * ν := by
  have h1 : QuotientGroup.mk' N u = QuotientGroup.mk' N (m * u * m⁻¹) := by
    rw [map_mul, map_mul, map_inv, Subgroup.mem_centralizer_singleton_iff.mp hc,
      mul_inv_cancel_right]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  exact ⟨_, h1, by group⟩

omit [Finite X] in
theorem isUniqueInvolution_mk {K : Subgroup X} {u : X} (hu : IsUniqueInvolution K u)
    (huN : u ∉ N) (hKN : K ⊓ N = ⊥) :
    IsUniqueInvolution (K.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N u) where
  mem := Subgroup.mem_map_of_mem _ hu.mem
  ne_one := fun h => huN ((QuotientGroup.eq_one_iff u).mp h)
  sq := by rw [← map_mul, hu.sq, map_one]
  unique := by
    rintro _ ⟨k, hk, rfl⟩ hkk
    have hk2 : k * k ∈ K ⊓ N :=
      ⟨K.mul_mem hk hk, (QuotientGroup.eq_one_iff _).mp (by rw [← map_mul] at hkk; exact hkk)⟩
    rw [hKN, Subgroup.mem_bot] at hk2
    rcases hu.unique k hk hk2 with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]

variable {K : Subgroup X} {u : X}

omit [Finite X] in
theorem isPGroup_of_mem_conjClass (hq : Nonempty (↥K ≃* QuaternionGroup 2)) :
    ∀ J ∈ CoreAssembly.conjClass K, IsPGroup 2 ↥J := by
  obtain ⟨eK⟩ := hq
  have h8 : Nat.card ↥K = 8 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rintro _ ⟨g, rfl⟩
  exact IsPGroup.of_card (n := 3) (by rw [Vtx.natCard_conjSub, h8]; norm_num)

theorem inf_eq_bot_of_mem_conjClass (hq : Nonempty (↥K ≃* QuaternionGroup 2))
    (hΩ : HypOmegaGen (CoreAssembly.conjClass K)) (hu : IsUniqueInvolution K u) (huN : u ∉ N) :
    ∀ J ∈ CoreAssembly.conjClass K, J ⊓ N = ⊥ := by
  refine fun J hJ => PhilipHall.Frame.TwinDisc.ExitE4.inf_eq_bot
    (isPGroup_of_mem_conjClass hq) hΩ ?_ hJ
  rintro _ ⟨g, rfl⟩ w hw hwN
  rw [hw.eq (hu.conj g)] at hwN
  apply huN
  have h := (inferInstance : N.Normal).conj_mem _ hwN g⁻¹
  simpa [mul_assoc] using h

theorem quatTwinDatum_mk (hNc : N ≤ Subgroup.center X)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass K)) (hq : Nonempty (↥K ≃* QuaternionGroup 2))
    (hu : IsUniqueInvolution K u) (huN : u ∉ N)
    (htw : ∀ L ∈ twinSet (CoreAssembly.conjClass K) K, L = K) :
    QuatTwinDatum (K.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N u) := by
  have h2 := isPGroup_of_mem_conjClass hq
  have hK := CoreAssembly.mem_conjClass_self K
  have hKN : K ⊓ N = ⊥ := inf_eq_bot_of_mem_conjClass hq hΩ hu huN K hK
  have hnab := PhilipHall.Frame.TwinDisc.ExitE4.exists_noncomm hΩ h2 hK
  have hfix : ∀ m : X, m * u * m⁻¹ = u → conjSub m K = K := by
    intro m hm
    refine htw _ ⟨⟨m, rfl⟩, u, hu, ?_⟩
    have h := hu.conj m
    rwa [hm] at h
  refine ⟨?_, isUniqueInvolution_mk hu huN hKN, ?_, ?_⟩
  · obtain ⟨eK⟩ := hq
    exact ⟨(AscQuot.quotRestrictEquiv hKN).symm.trans eK⟩
  · intro c hc
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N c
    obtain ⟨ν, hνN, hm⟩ := exists_mem_of_mk_mem_centralizer hc
    have hq' : u⁻¹ * (m * u * m⁻¹) = ν := by rw [hm]; group
    have hνc : ∀ y : X, y * ν = ν * y := Subgroup.mem_center_iff.mp (hNc hνN)
    rcases PhilipHall.Frame.TwinDisc.ExitE4.twin_clause_central hΩ h2 hK hu hnab hq' hνc with
      h | h
    · left
      rw [conjSub_map, h]
    · right
      rw [conjSub_map]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h x hx y hy]
  · intro c hc
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N c
    obtain ⟨ν, hνN, hm⟩ := exists_mem_of_mk_mem_centralizer hc
    have hνc : ∀ y : X, y * ν = ν * y := Subgroup.mem_center_iff.mp (hNc hνN)
    have hu2 : u * u = 1 := hu.sq
    have hν2 : ν * ν = 1 := by
      calc ν * ν = u * u * (ν * ν) := by rw [hu2, one_mul]
        _ = u * (u * ν) * ν := by group
        _ = u * (ν * u) * ν := by rw [hνc u]
        _ = (u * ν) * (u * ν) := by group
        _ = (m * u * m⁻¹) * (m * u * m⁻¹) := by rw [hm]
        _ = m * (u * u) * m⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hmν : m * ν * m⁻¹ = ν := by rw [hνc m, mul_inv_cancel_right]
    have hmm : m * m * u * (m * m)⁻¹ = u := by
      calc m * m * u * (m * m)⁻¹ = m * (m * u * m⁻¹) * m⁻¹ := by group
        _ = m * (u * ν) * m⁻¹ := by rw [hm]
        _ = (m * u * m⁻¹) * (m * ν * m⁻¹) := by group
        _ = u * ν * ν := by rw [hm, hmν]
        _ = u := by rw [mul_assoc, hν2, mul_one]
    rw [← map_mul, conjSub_map, hfix (m * m) hmm]

section Model

variable {M : Type} [Group M] [Finite M]

theorem conjSub_mem_omegaNbr_iff {G : Type} [Group G] (φ : M →* G) (hφ : Function.Injective φ)
    {K : Subgroup M} (h2 : IsPGroup 2 ↥K) (m : M) :
    conjSub m K ∈ omegaNbr (CoreAssembly.conjClass K) K ↔
      conjSub (φ m) (K.map φ) ≠ K.map φ ∧
        conjSub (φ m) (K.map φ) ≤ Subgroup.normalizer ((K.map φ : Subgroup G) : Set G) := by
  rw [Vtx.mem_omegaNbr_conjClass_iff h2, conjSub_map]
  constructor
  · rintro ⟨-, hne, hle⟩
    exact ⟨fun h => hne (Subgroup.map_injective hφ h),
      (Vtx.map_le_normalizer_map_iff φ hφ).mpr hle⟩
  · rintro ⟨hne, hle⟩
    exact ⟨⟨m, rfl⟩, fun h => hne (by rw [h]), (Vtx.map_le_normalizer_map_iff φ hφ).mp hle⟩

theorem ncard_omegaNbr_PSp (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) {K : Subgroup M} {s : M}
    (hd : QuatTwinDatum K s) : (omegaNbr (CoreAssembly.conjClass K) K).ncard = 1 := by
  obtain ⟨e⟩ := CFSG.EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36 hM
  obtain ⟨φ, hφ, hrange, hKc⟩ := E4Sp6.exists_emb e hd
  have h2 := isPGroup_of_mem_conjClass hd.q8 K (CoreAssembly.mem_conjClass_self K)
  have hiff := conjSub_mem_omegaNbr_iff φ hφ h2
  rw [hKc] at hiff
  obtain ⟨m₀, hm₀⟩ : E4Sp6.twin () ∈ φ.range := hrange ▸ E4Sp6.ws_mem 11
  rw [Set.ncard_eq_one]
  refine ⟨conjSub m₀ K, Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · rw [hiff, hm₀]
    exact E4Sp6.edge
  · intro J hJ
    obtain ⟨m, rfl⟩ := hJ.1
    obtain ⟨hne, hle⟩ := (hiff m).mp hJ
    have h := E4Sp6.eq_twin_of_le_normalizer (hrange ▸ ⟨m, rfl⟩) hne hle
    rw [← hm₀, ← hKc, conjSub_map, conjSub_map] at h
    exact Subgroup.map_injective hφ h

theorem ncard_omegaNbr_POmegaPlus (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1)
    {K : Subgroup M} {s : M} (hd : QuatTwinDatum K s) :
    (omegaNbr (CoreAssembly.conjClass K) K).ncard = 3 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hM
  obtain ⟨φ, hφ, hrange, hKc⟩ := E4O8.exists_emb e hd
  have h2 := isPGroup_of_mem_conjClass hd.q8 K (CoreAssembly.mem_conjClass_self K)
  have hiff := conjSub_mem_omegaNbr_iff φ hφ h2
  rw [hKc] at hiff
  have hpre : ∀ g ∈ omegaT, ∃ m : M, φ m = g := fun g hg => MonoidHom.mem_range.mp (hrange ▸ hg)
  have hinj : ∀ m m' : M, conjSub (φ m) E4O8.K0 = conjSub (φ m') E4O8.K0 →
      conjSub m K = conjSub m' K := by
    intro m m' h
    rw [← hKc, conjSub_map, conjSub_map] at h
    exact Subgroup.map_injective hφ h
  obtain ⟨a, ha⟩ := hpre _ (E4O8.root_mem 0)
  obtain ⟨b, hb⟩ := hpre _ (E4O8.root_mem 4)
  obtain ⟨c, hc⟩ := hpre _ (E4O8.root_mem 6)
  obtain ⟨n₁, hn₁⟩ := hpre _ (E4O8.ws_mem 1)
  obtain ⟨n₃, hn₃⟩ := hpre _ (E4O8.ws_mem 3)
  obtain ⟨n₄, hn₄⟩ := hpre _ (E4O8.ws_mem 4)
  obtain ⟨a1, a2, b1, b2, hab⟩ := E4O8.two_nbrs
  obtain ⟨c1, c2, hac, hbc⟩ := E4O8.three_nbrs
  apply le_antisymm
  · have hsub : omegaNbr (CoreAssembly.conjClass K) K ⊆
        {conjSub n₁ K, conjSub n₃ K, conjSub n₄ K} := by
      intro J hJ
      obtain ⟨m, rfl⟩ := hJ.1
      obtain ⟨hne, hle⟩ := (hiff m).mp hJ
      obtain ⟨k, hk, he⟩ := E4O8.mem_twins_of_le_normalizer (hrange ▸ ⟨m, rfl⟩) hne hle
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact Or.inl (hinj _ _ (by rw [he, hn₁]))
      · exact Or.inr (Or.inl (hinj _ _ (by rw [he, hn₃])))
      · exact Or.inr (Or.inr (hinj _ _ (by rw [he, hn₄])))
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
    rw [Set.ncard_singleton]
  · have hne : ∀ m m' : M, conjSub (φ m) E4O8.K0 ≠ conjSub (φ m') E4O8.K0 →
        conjSub m K ≠ conjSub m' K := fun m m' h e => h (by rw [← hKc, conjSub_map,
          conjSub_map, e])
    have hsup : ({conjSub a K, conjSub b K, conjSub c K} : Set (Subgroup M)) ⊆
        omegaNbr (CoreAssembly.conjClass K) K := by
      rintro J (rfl | rfl | rfl)
      · exact (hiff a).mpr (by rw [ha]; exact ⟨a1, a2⟩)
      · exact (hiff b).mpr (by rw [hb]; exact ⟨b1, b2⟩)
      · exact (hiff c).mpr (by rw [hc]; exact ⟨c1, c2⟩)
    have h3 : ({conjSub a K, conjSub b K, conjSub c K} : Set (Subgroup M)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨_, _, _, hne a b (by rw [ha, hb]; exact hab),
        hne a c (by rw [ha, hc]; exact hac), hne b c (by rw [hb, hc]; exact hbc), rfl⟩
    rw [← h3]
    exact Set.ncard_le_ncard hsup (Set.toFinite _)

omit [Finite M] in
theorem commutes_of_mem_insert (hNI : E4QuatNbrInv M) {K : Subgroup M} {s : M}
    (hd : QuatTwinDatum K s) {B B' : Subgroup M}
    (hB : B ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K))
    (hB' : B' ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K)) (hne : B ≠ B') :
    Commutes B B' := by
  have hcs : ∀ L ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K),
      ∃ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = L := by
    rintro L (rfl | hL)
    · exact ⟨1, Subgroup.one_mem _, conjSub_one L⟩
    · obtain ⟨g, rfl⟩ := hL.1
      refine ⟨g, ?_, rfl⟩
      have h1 := (hNI K s hd _ hL).eq (hd.inv.conj g)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * s = (g * s * g⁻¹) * g := by group
        _ = s * g := by rw [← h1]
  obtain ⟨c, hc, rfl⟩ := hcs B hB
  obtain ⟨c', hc', rfl⟩ := hcs B' hB'
  have hcc : c⁻¹ * c' ∈ Subgroup.centralizer ({s} : Set M) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hc'
  rcases hd.twins _ hcc with h | h
  · refine absurd ?_ hne
    rw [← mul_inv_cancel_left c c', conjSub_mul, h]
  · intro x hx y hy
    rw [mem_conjSub_iff] at hx hy
    have hy' : c⁻¹ * y * c ∈ conjSub (c⁻¹ * c') K := by
      rw [mem_conjSub_iff]
      have e : (c⁻¹ * c')⁻¹ * (c⁻¹ * y * c) * (c⁻¹ * c') = c'⁻¹ * y * c' := by group
      rw [e]
      exact hy
    have hcomm := h _ hx _ hy'
    calc x * y = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by rw [hcomm]
      _ = y * x := by group

end Model

end E4Cover

theorem e4CoverNbrs_proved :
    ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X) [N.Normal] (K : Subgroup X) (u : X),
      IsPGroup 2 ↥N → N ≤ Subgroup.center X → HypOmegaGen (CoreAssembly.conjClass K) →
      Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K u → u ∉ N →
      (∀ L ∈ twinSet (CoreAssembly.conjClass K) K, L = K) →
      PhilipHall.QuaternionBridge.ExLie (X ⧸ N) →
        (CFSG.Blueprint.LieModel (X ⧸ N) .PSp 3 2 1 →
            (omegaNbr (CoreAssembly.conjClass K) K).ncard = 1) ∧
          (CFSG.Blueprint.LieModel (X ⧸ N) .POmegaPlus 4 2 1 →
            (omegaNbr (CoreAssembly.conjClass K) K).ncard = 3) ∧
          ∀ B ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K),
            ∀ B' ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K), B ≠ B' →
              ∀ x ∈ B, ∀ y ∈ B', x * y * x⁻¹ * y⁻¹ ∈ N := by
  intro X _ _ N _ K u _ hNc hΩ hq hu huN htw hM
  have h2 := E4Cover.isPGroup_of_mem_conjClass hq
  have hmeet := E4Cover.inf_eq_bot_of_mem_conjClass (N := N) hq hΩ hu huN
  have c := PhilipHall.Frame.TwinDisc.ExitE4.centQuotGen hΩ h2 hNc hmeet
  have hd := E4Cover.quatTwinDatum_mk hNc hΩ hq hu huN htw
  have hK := CoreAssembly.mem_conjClass_self K
  have hfam : quotFamily (CoreAssembly.conjClass K) N =
      CoreAssembly.conjClass (K.map (QuotientGroup.mk' N)) :=
    PhilipHall.QuaternionBridge.image_conjClass (N := N) K
  have himage : (fun J : Subgroup X => J.map (QuotientGroup.mk' N)) ''
      omegaNbr (CoreAssembly.conjClass K) K =
      omegaNbr (CoreAssembly.conjClass (K.map (QuotientGroup.mk' N)))
        (K.map (QuotientGroup.mk' N)) := by
    ext Jb
    constructor
    · rintro ⟨J, hJ, rfl⟩
      have h := c.omegaNbr_map hK hJ
      rwa [hfam] at h
    · intro hJb
      rw [← hfam] at hJb
      obtain ⟨J, hJ, rfl⟩ := hJb.1
      exact ⟨J, c.omegaNbr_of_map hK hJ hJb, rfl⟩
  have hinj : Set.InjOn (fun J : Subgroup X => J.map (QuotientGroup.mk' N))
      (omegaNbr (CoreAssembly.conjClass K) K) :=
    fun J hJ J' hJ' h => c.eq_of_map J hJ.1 J' hJ'.1 h
  have hcard : (omegaNbr (CoreAssembly.conjClass K) K).ncard =
      (omegaNbr (CoreAssembly.conjClass (K.map (QuotientGroup.mk' N)))
        (K.map (QuotientGroup.mk' N))).ncard := by
    rw [← himage, hinj.ncard_image]
  refine ⟨fun hP => hcard ▸ E4Cover.ncard_omegaNbr_PSp hP hd,
    fun hP => hcard ▸ E4Cover.ncard_omegaNbr_POmegaPlus hP hd, ?_⟩
  intro B hB B' hB' hne x hx y hy
  have hmemΦ : ∀ L ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K),
      L ∈ CoreAssembly.conjClass K := by
    rintro L (rfl | hL)
    · exact hK
    · exact hL.1
  have hmapmem : ∀ L ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K),
      L.map (QuotientGroup.mk' N) ∈ insert (K.map (QuotientGroup.mk' N))
        (omegaNbr (CoreAssembly.conjClass (K.map (QuotientGroup.mk' N)))
          (K.map (QuotientGroup.mk' N))) := by
    rintro L (rfl | hL)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (himage ▸ ⟨L, hL, rfl⟩)
  have hne' : B.map (QuotientGroup.mk' N) ≠ B'.map (QuotientGroup.mk' N) :=
    fun h => hne (c.eq_of_map B (hmemΦ B hB) B' (hmemΦ B' hB') h)
  have hcomm := E4Cover.commutes_of_mem_insert (e4QuatNbrInv_of_exLie hM) hd (hmapmem B hB)
    (hmapmem B' hB') hne'
  have h := hcomm _ (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy)
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.ClassicalInvolution.Q3.Sec13End16A
public import CFSG.ClassicalInvolution.Q3.Sec13EndMin
public import CFSG.ClassicalInvolution.Q3.TL4AECover
public import CFSG.ClassicalInvolution.Q3.Sec13End16F
import CFSG.ClassicalInvolution.Q3.Sec13AECoverEven
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfMembers

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

namespace EndHyp

variable {Ω : Set (Subgroup G)}

theorem oddCore_pSpan_centMembers_eq_bot (h : EndHyp Ω) (h9 : Perp9 Ω) {K K' : Subgroup G}
    {z : G} (s : TwinSit Ω K K' z) (h13 : zGroup Ω ≠ eGroup Ω K) {a : G} (ha : a ∈ zGroup Ω)
    (ha1 : a ≠ 1) : classicalInvolutionOddCore ↥(pSpan (centMembers Ω a)) = ⊥ :=
  oddCore_centMembers_eq_bot h h9 s h13 ha ha1

end EndHyp

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

private theorem e16b_comm_normalizer (c : Sit16 Ω K K' W z u e g) {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) : x * e = e * x := by
  have he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← c.data.he]
    exact Subgroup.subset_closure rfl
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp he.2
  have hyc := Subgroup.mem_center_iff.mp hy ⟨x, hx⟩
  have h1 : x * (y : G) = (y : G) * x := congrArg Subtype.val hyc
  rw [show (y : G) = e from hye] at h1
  exact h1

private theorem e16b_le_centralizer (c : Sit16 Ω K K' W z u e g) {L : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (W : Set G)) : L ≤ Subgroup.centralizer ({e} : Set G) :=
  fun _ hx => Subgroup.mem_centralizer_singleton_iff.mpr (e16b_comm_normalizer c (hL hx))

private theorem e16b_twin_of_commutes (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    {M L : Subgroup G} (hM : M ∈ Ω) (hMz : IsUniqueInvolution M z) (hL : L ∈ Ω)
    (hc : Commutes M L) : L ∈ twinSet Ω K := by
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL
  have hzj : z = j := h9 M hM L hL hc z j hMz hj
  refine ⟨hL, z, s.isInv, ?_⟩
  rw [hzj]
  exact hj

theorem dSet_mem_centMembers (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) :
    ∀ R ∈ DSet Ω W, R ∈ centMembers Ω e :=
  fun _ hR => c.dSet_subset_centMembers h hR

theorem centMembers_oneClass (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    ∀ L ∈ centMembers Ω e, ∀ L' ∈ centMembers Ω e,
      ∃ x ∈ pSpan (centMembers Ω e), conjSub x L = L' := by
  have s := c.twin
  have he1 : e ≠ 1 := c.data.he1
  have hlt : Nat.card ↥(pSpan (centMembers Ω e)) < Nat.card G :=
    h.toStarHyp.card_pSpan_centMembers_lt he1
  have hinv : ∀ L ∈ centMembers Ω e, ∀ x ∈ pSpan (centMembers Ω e),
      conjSub x L ∈ centMembers Ω e := fun _ hL _ hx => h.toStarHyp.conjSub_mem_centMembers hL hx
  have hPΩ : centMembers Ω e ⊆ Ω := fun _ hL => hL.1
  have hle : (⨆ R ∈ DSet Ω W, R) ≤ Subgroup.normalizer (W : Set G) :=
    iSup₂_le fun R hR => hR.2
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := hle c.data.hg
  have hKN : K ≤ Subgroup.normalizer (W : Set G) :=
    (h.mem_dSet_of_mem c.data.hW s.mem s.isInv c.data.hzW).2
  have hK'N : K' ≤ Subgroup.normalizer (W : Set G) :=
    (h.mem_dSet_of_mem c.data.hW s.mem_twin.1 s.mem_twin.2 c.data.hzW).2
  have hJN : conjSub g K ≤ Subgroup.normalizer (W : Set G) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have hy' := Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN (hKN hy)) (Subgroup.inv_mem _ hgN)
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at hy'
  have hKP : K ∈ centMembers Ω e :=
    Generic.mem_centMembers.mpr ⟨s.mem, e16b_le_centralizer c hKN⟩
  have hK'P : K' ∈ centMembers Ω e :=
    Generic.mem_centMembers.mpr ⟨s.mem_twin.1, e16b_le_centralizer c hK'N⟩
  have hJ'P : conjSub g K ∈ centMembers Ω e :=
    Generic.mem_centMembers.mpr ⟨h.thmD.hyp.conjInvariant g K s.mem, e16b_le_centralizer c hJN⟩
  have hJ'ne : conjSub g K ∉ twinSet Ω K := by
    rintro ⟨-, w, hw, hJw⟩
    have hwz : w = z := hw.eq s.isInv
    rw [hwz] at hJw
    have hzue : z = u * e := (hJw.eq (s.isInv.conj g)).trans c.data.hgt
    apply c.e_not_mem
    have he' : e = u * z := by
      rw [hzue, ← mul_assoc, c.data.hu2, one_mul]
    rw [he']
    exact Subgroup.mul_mem _ c.data.hu (Subgroup.mem_sup_left s.isInv.mem)
  have hrelKJ : ∃ x ∈ pSpan (centMembers Ω e), conjSub x K = conjSub g K := by
    by_contra hnc
    have hcom := h.toStarHyp.commutes_of_not_conj hPΩ hinv hlt hKP hJ'P hnc
    exact hJ'ne (e16b_twin_of_commutes h h9 s s.mem s.isInv (h.thmD.hyp.conjInvariant g K s.mem)
      hcom)
  have hrelK'J : ∃ x ∈ pSpan (centMembers Ω e), conjSub x K' = conjSub g K := by
    by_contra hnc
    have hcom := h.toStarHyp.commutes_of_not_conj hPΩ hinv hlt hK'P hJ'P hnc
    exact hJ'ne (e16b_twin_of_commutes h h9 s s.mem_twin.1 s.mem_twin.2
      (h.thmD.hyp.conjInvariant g K s.mem) hcom)
  have hrelKK' : ∃ x ∈ pSpan (centMembers Ω e), conjSub x K = K' := by
    obtain ⟨x, hx, hxK⟩ := hrelKJ
    obtain ⟨y, hy, hyK'⟩ := hrelK'J
    refine ⟨y⁻¹ * x, Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hx, ?_⟩
    rw [conjSub_mul, hxK, ← hyK', conjSub_inv_conjSub]
  have hrelK : ∀ L ∈ centMembers Ω e, ∃ x ∈ pSpan (centMembers Ω e), conjSub x K = L := by
    intro L hL
    by_cases hc : ∃ x ∈ pSpan (centMembers Ω e), conjSub x K = L
    · exact hc
    · have hcom := h.toStarHyp.commutes_of_not_conj hPΩ hinv hlt hKP hL hc
      have hmem := e16b_twin_of_commutes h h9 s s.mem s.isInv hL.1 hcom
      rw [s.twin] at hmem
      rcases hmem with h1 | h1
      · exact (hc ⟨1, Subgroup.one_mem _, by rw [conjSub_one, h1]⟩).elim
      · rw [Set.mem_singleton_iff] at h1
        exact (hc (by rw [h1]; exact hrelKK')).elim
  intro L hL L' hL'
  obtain ⟨a, ha, haL⟩ := hrelK L hL
  obtain ⟨b, hb, hbL⟩ := hrelK L' hL'
  refine ⟨b * a⁻¹, Subgroup.mul_mem _ hb (Subgroup.inv_mem _ ha), ?_⟩
  rw [conjSub_mul, ← haL, conjSub_inv_conjSub, hbL]

theorem exists_member_le_centralizer_not_le_normalizer (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ R ∈ Ω, R ≤ Subgroup.centralizer ({e} : Set G) ∧ ¬ R ≤ Subgroup.normalizer (W : Set G) :=
  exists_member_centralizer_not_normalizer c h h9 h13

private theorem e16b6_comm_normalizer (c : Sit16 Ω K K' W z u e g) {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) : x * e = e * x := by
  have he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← c.data.he]
    exact Subgroup.subset_closure rfl
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp he.2
  have hyc := Subgroup.mem_center_iff.mp hy ⟨x, hx⟩
  have h1 : x * (y : G) = (y : G) * x := congrArg Subtype.val hyc
  rw [show (y : G) = e from hye] at h1
  exact h1

private theorem e16b6_le_centralizer (c : Sit16 Ω K K' W z u e g) {L : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (W : Set G)) : L ≤ Subgroup.centralizer ({e} : Set G) :=
  fun _ hx => Subgroup.mem_centralizer_singleton_iff.mpr (e16b6_comm_normalizer c (hL hx))

private theorem e16b6_mem_sup {K K' : Subgroup G} (hc : Commutes K K') {x : G}
    (hx : x ∈ K ⊔ K') : ∃ k ∈ K, ∃ k' ∈ K', x = k * k' := by
  let P : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ k' ∈ K', x = k * k'}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, k₁', hk₁', rfl⟩ ⟨k₂, hk₂, k₂', hk₂', rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₁' * k₂', K'.mul_mem hk₁' hk₂', ?_⟩
        have e := hc k₂ hk₂ k₁' hk₁'
        calc k₁ * k₁' * (k₂ * k₂') = k₁ * (k₁' * k₂) * k₂' := by group
          _ = k₁ * (k₂ * k₁') * k₂' := by rw [← e]
          _ = k₁ * k₂ * (k₁' * k₂') := by group
      one_mem' := ⟨1, K.one_mem, 1, K'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, k', hk', rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k'⁻¹, K'.inv_mem hk', ?_⟩
        have e := hc k hk k' hk'
        calc (k * k')⁻¹ = k'⁻¹ * k⁻¹ := by group
          _ = k⁻¹ * k'⁻¹ := by
            have e' : (k' * k)⁻¹ = (k * k')⁻¹ := by rw [e]
            rw [mul_inv_rev, mul_inv_rev] at e'
            exact e'.symm }
  have hle : K ⊔ K' ≤ P := by
    refine sup_le (fun k hk => ⟨k, hk, 1, K'.one_mem, by simp⟩)
      (fun k' hk' => ⟨1, K.one_mem, k', hk', by simp⟩)
  exact hle hx

private theorem e16b6_memb (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) :
    K ∈ centMembers Ω e ∧ K' ∈ centMembers Ω e ∧ conjSub g K ∈ centMembers Ω e := by
  have hle : (⨆ R ∈ DSet Ω W, R) ≤ Subgroup.normalizer (W : Set G) :=
    iSup₂_le fun R hR => hR.2
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := hle c.data.hg
  have hKN : K ≤ Subgroup.normalizer (W : Set G) :=
    (h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW).2
  have hK'N : K' ≤ Subgroup.normalizer (W : Set G) :=
    (h.mem_dSet_of_mem c.data.hW c.twin.mem_twin.1 c.twin.mem_twin.2 c.data.hzW).2
  have hJN : conjSub g K ≤ Subgroup.normalizer (W : Set G) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have hy' := Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN (hKN hy)) (Subgroup.inv_mem _ hgN)
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at hy'
  refine ⟨Generic.mem_centMembers.mpr ⟨c.twin.mem, e16b6_le_centralizer c hKN⟩,
    Generic.mem_centMembers.mpr ⟨c.twin.mem_twin.1, e16b6_le_centralizer c hK'N⟩,
    Generic.mem_centMembers.mpr ⟨h.thmD.hyp.conjInvariant g K c.twin.mem,
      e16b6_le_centralizer c hJN⟩⟩

private theorem e16b6_e_mem (c : Sit16 Ω K K' W z u e g)
    (hKP : K ∈ centMembers Ω e) (hK'P : K' ∈ centMembers Ω e)
    (hJP : conjSub g K ∈ centMembers Ω e)
    (hJinv : IsUniqueInvolution (conjSub g K) (u * e)) :
    e ∈ pSpan (centMembers Ω e) := by
  have hu : u ∈ pSpan (centMembers Ω e) :=
    (sup_le (le_pSpan hKP) (le_pSpan hK'P)) c.data.hu
  have hte : u * e ∈ pSpan (centMembers Ω e) := le_pSpan hJP hJinv.mem
  have h1 : e = u * (u * e) := by rw [← mul_assoc, c.data.hu2, one_mul]
  have h2 : u * (u * e) ∈ pSpan (centMembers Ω e) := Subgroup.mul_mem _ hu hte
  rwa [← h1] at h2

private theorem e16b6_false_of_odd (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    {n : ℕ} (hn : 5 ≤ n) (hodd : Odd n)
    (φ : ↥(pSpan (centMembers Ω e)) →* AE.AEQ n)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (centMembers Ω e)))
    (hcen : ∀ m ∈ φ.range, (∀ m' ∈ φ.range, m * m' = m' * m) → m = 1)
    (hlab : ∀ L ∈ centMembers Ω e, ∃ (α : Finset (Fin n)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (centMembers Ω e))).map φ = AE.memBar α hα b)
    (hKP : K ∈ centMembers Ω e) (hK'P : K' ∈ centMembers Ω e)
    (hJP : conjSub g K ∈ centMembers Ω e) : False := by
  have hn8 : n ≠ 8 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hJinv : IsUniqueInvolution (conjSub g K) (u * e) := by
    have := c.twin.isInv.conj g
    rwa [c.data.hgt] at this
  have he := e16b6_e_mem c hKP hK'P hJP hJinv
  have hXC : pSpan (centMembers Ω e) ≤ Subgroup.centralizer ({e} : Set G) :=
    pSpan_le fun L hL => hL.2
  have hcomm : Commutes K K' := c.twin.commutes h
  have hzK : IsUniqueInvolution K z := c.twin.isInv
  have hzK' : IsUniqueInvolution K' z := c.twin.mem_twin.2
  have hKX : K ≤ pSpan (centMembers Ω e) := le_pSpan hKP
  have hK'X : K' ≤ pSpan (centMembers Ω e) := le_pSpan hK'P
  have hJX : conjSub g K ≤ pSpan (centMembers Ω e) := le_pSpan hJP
  have hu : u ∈ pSpan (centMembers Ω e) := (sup_le hKX hK'X) c.data.hu
  have hte : u * e ∈ pSpan (centMembers Ω e) := hJX hJinv.mem
  have hzX : z ∈ pSpan (centMembers Ω e) := hKX hzK.mem
  have hcenter : ∀ x ∈ pSpan (centMembers Ω e), x * e = e * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXC hx)
  have hφe : φ ⟨e, he⟩ = 1 := by
    apply hcen _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    intro m' hm'
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hm'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcenter x x.2).symm
  have hcardK : Nat.card K = 8 := h.card_eq_eight c.twin.mem
  have hK'Ω : K' ∈ Ω := c.twin.mem_twin.1
  have hcardK' : Nat.card K' = 8 := h.card_eq_eight hK'Ω
  have hcardJ : Nat.card (conjSub g K) = 8 := h.card_eq_eight hJP.1
  obtain ⟨α, hα, b, hKlab⟩ := hlab K hKP
  obtain ⟨β, hβ, b', hK'lab⟩ := hlab K' hK'P
  obtain ⟨α', hα', b'', hJlab⟩ := hlab (conjSub g K) hJP
  have hz1 := phi_map_eq_zBar φ hn hKP hcardK hKlab hzK
  have hz2 := phi_map_eq_zBar φ hn hK'P hcardK' hK'lab hzK'
  have hαβ : α = β := AE.eq_of_zBar_eq hn8 (hz1.symm.trans hz2)
  subst hαβ
  have hz3 := phi_map_eq_zBar φ hn hJP hcardJ hJlab hJinv
  have hkey : φ ⟨u, hu⟩ = φ ⟨u * e, hte⟩ := by
    have h1 : φ ⟨e, he⟩ = φ ⟨u, hu⟩ * φ ⟨u * e, hte⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by show e = u * (u * e); rw [← mul_assoc, c.data.hu2, one_mul])
    rw [hφe] at h1
    have hsq : φ ⟨u * e, hte⟩ * φ ⟨u * e, hte⟩ = 1 := by
      have h2 : (⟨u * e, hte⟩ * ⟨u * e, hte⟩ : ↥(pSpan (centMembers Ω e))) = 1 :=
        Subtype.ext hJinv.sq
      rw [← map_mul, h2, map_one]
    calc φ ⟨u, hu⟩ = (φ ⟨u * e, hte⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
      _ = φ ⟨u * e, hte⟩ := inv_eq_of_mul_eq_one_right hsq
  obtain ⟨k, hkK, k', hk'K', hkk⟩ := e16b6_mem_sup hcomm c.data.hu
  have hkX : k ∈ pSpan (centMembers Ω e) := hKX hkK
  have hk'X : k' ∈ pSpan (centMembers Ω e) := hK'X hk'K'
  have hk_mem : φ ⟨k, hkX⟩ ∈ (AE.memAt α hα b).map (AE.mkQ n) := by
    have : φ ⟨k, hkX⟩ ∈ (K.subgroupOf (pSpan (centMembers Ω e))).map φ :=
      Subgroup.mem_map.mpr ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.mpr hkK, rfl⟩
    rw [hKlab] at this
    exact this
  have hk'_mem : φ ⟨k', hk'X⟩ ∈ (AE.memAt α hα b').map (AE.mkQ n) := by
    have : φ ⟨k', hk'X⟩ ∈ (K'.subgroupOf (pSpan (centMembers Ω e))).map φ :=
      Subgroup.mem_map.mpr ⟨⟨k', hk'X⟩, Subgroup.mem_subgroupOf.mpr hk'K', rfl⟩
    rw [hK'lab] at this
    exact this
  obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hk_mem
  obtain ⟨y, hy, hyk'⟩ := Subgroup.mem_map.mp hk'_mem
  have hmk : AE.mkQ n (x * y) = φ ⟨u, hu⟩ := by
    rw [map_mul, hxk, hyk', ← map_mul]
    congr 1
    exact Subtype.ext hkk.symm
  have hmemAt_le : ∀ (γ : Finset (Fin n)) (hγ : γ.card = 4) (c' : Bool),
      AE.memAt γ hγ c' ≤ AE.aeSub n := by
    intro γ hγ c'
    cases c'
    · exact AE.memKStar_le_aeSub _
    · exact AE.memK_le_aeSub _
  have hxa : x ∈ AE.aeSub n := hmemAt_le _ _ _ hx
  have hya : y ∈ AE.aeSub n := hmemAt_le _ _ _ hy
  have hZa : AE.zOf (AE.emb α' hα') ∈ AE.aeSub n :=
    hmemAt_le _ _ _ (AE.zOf_mem_memAt α' hα' b'')
  have hsupp : AE.SupportedOn (x * y) (Set.range (AE.emb α hα)) :=
    AE.SupportedOn.mul (AE.supportedOn_of_mem_memAt hx) (AE.supportedOn_of_mem_memAt hy)
  have hZ' : AE.mkQ n (x * y) = AE.mkQ n (AE.zOf (AE.emb α' hα')) := by
    rw [hmk, hkey, hz3]
    rfl
  have hprod : (x * y)⁻¹ * AE.zOf (AE.emb α' hα') ∈ AE.aeSub n :=
    (AE.aeSub n).mul_mem ((AE.aeSub n).inv_mem ((AE.aeSub n).mul_mem hxa hya)) hZa
  rcases (AE.mkQ_eq_iff).mp hZ' with h1 | h1
  swap
  ·
    exfalso
    have hall : AE.Wr.allOnes n ∈ AE.aeSub n := h1 ▸ hprod
    have hw : (AE.Wr.allOnes n).wsum = 0 := ((AE.mem_aeSub).mp hall).1
    have hw' : (AE.Wr.allOnes n).wsum = ((n : ℕ) : ZMod 2) := by
      simp [AE.Wr.wsum, AE.Wr.allOnes]
    rw [hw'] at hw
    exact (Nat.not_even_iff_odd.mpr hodd) (ZMod.natCast_eq_zero_iff_even.mp hw)
  have hae : x * y = AE.zOf (AE.emb α' hα') := inv_mul_eq_one.mp h1
  have hsub : α' ⊆ α := by
    intro i hi
    by_contra hi'
    have hiα : i ∉ Set.range (AE.emb α hα) := by
      rw [AE.range_emb]
      exact hi'
    have hv : (x * y).vec i = 0 := (hsupp i hiα).1
    have hv1 : (x * y).vec i = 1 := by
      rw [hae, AE.zOf_vec_apply, if_pos]
      rw [AE.range_emb]
      exact hi
    rw [hv1] at hv
    exact one_ne_zero hv
  have heq : α' = α := Finset.eq_of_subset_of_card_le hsub (by rw [hα, hα'])
  subst heq
  have hφu : φ ⟨u, hu⟩ = AE.zBar α' hα' := by
    rw [← hmk, hae]
    rfl
  have hwker : (⟨u, hu⟩ * ⟨z, hzX⟩ : ↥(pSpan (centMembers Ω e))) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, hφu, hz1, AE.zBar_mul_self]
  have hcenter_uz : ∀ x ∈ K, x * (u * z) = (u * z) * x := by
    intro x hx
    have h1 := Subgroup.mem_center_iff.mp (hker hwker) ⟨x, hKX hx⟩
    exact congrArg Subtype.val h1
  have hzk' : z * k' = k' * z := hcomm z hzK.mem k' hk'K'
  have hu_eq : u * z = (k * z) * k' := by
    rw [hkk, mul_assoc, ← hzk', ← mul_assoc]
  have hcK : ∀ x ∈ K, (k * z) * x = x * (k * z) := by
    intro x hx
    have h1 := hcenter_uz x hx
    rw [hu_eq] at h1
    have h2 : x * (k * z) * k' = (k * z) * x * k' := by
      calc x * (k * z) * k' = x * ((k * z) * k') := by group
        _ = ((k * z) * k') * x := h1
        _ = (k * z) * (k' * x) := by group
        _ = (k * z) * (x * k') := by rw [(hcomm x hx k' hk'K').symm]
        _ = (k * z) * x * k' := by group
    exact (mul_right_cancel h2).symm
  have hkzK : k * z ∈ K := K.mul_mem hkK hzK.mem
  have hsq : (k * z) * (k * z) = 1 :=
    ((h.isQuatSub_of_mem c.twin.mem)).sq_eq_one_of_central hkzK hcK
  have huK' : u ∈ K' := by
    rcases hzK.unique (k * z) hkzK hsq with h1 | h1
    · have hk : k = z := mul_right_cancel (h1.trans hzK.sq.symm)
      rw [hkk, hk]
      exact K'.mul_mem hzK'.mem hk'K'
    · have hk : k = 1 := mul_right_cancel (h1.trans (one_mul z).symm)
      rw [hkk, hk, one_mul]
      exact hk'K'
  rcases hzK'.unique u huK' c.data.hu2 with h1 | h1
  · exact c.data.hu1 h1
  · exact c.data.huz h1


private theorem e16b6_label_inj_gen {Ω' P : Set (Subgroup G)} {n : ℕ}
    (hΩ : HypOmegaGen Ω') (h2 : ∀ L ∈ Ω', IsPGroup 2 ↥L) (hPΩ : P ⊆ Ω')
    (I : AEIdent P n) (hk : IsPGroup 2 ↥I.φ.ker)
    (hnab : ∀ L ∈ P, ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) :
    ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L' := by
  intro L hL L' hL' he
  by_contra hne
  set Q := (L.subgroupOf (pSpan P)).map I.φ with hQ
  have hQ2 : IsPGroup 2 ↥Q :=
    ((h2 L (hPΩ hL)).of_equiv (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).symm).map _
  have hH2 : IsPGroup 2 ↥((Q.comap I.φ).map (pSpan P).subtype) :=
    (hQ2.comap_of_ker_isPGroup I.φ hk).map _
  have hLH : L ≤ (Q.comap I.φ).map (pSpan P).subtype := fun l hl =>
    ⟨⟨l, le_pSpan hL hl⟩, I.mem_map hL hl, rfl⟩
  have hL'H : L' ≤ (Q.comap I.φ).map (pSpan P).subtype := fun l hl =>
    ⟨⟨l, le_pSpan hL' hl⟩, by
      show I.φ ⟨l, le_pSpan hL' hl⟩ ∈ Q
      rw [he]
      exact I.mem_map hL' hl, rfl⟩
  have hc : Commutes L L' :=
    TL4.commutes_of_le_two hΩ h2 (hPΩ hL) (hPΩ hL') hne hH2 hLH hL'H
  have hall : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    have hbQ : I.φ ⟨b, le_pSpan hL hb⟩ ∈ (L'.subgroupOf (pSpan P)).map I.φ := by
      rw [← he]
      exact I.mem_map hL hb
    obtain ⟨y, hy, hyb⟩ := hbQ
    have hyL' : (y : G) ∈ L' := Subgroup.mem_subgroupOf.mp hy
    have hk0 : (⟨b, le_pSpan hL hb⟩ : ↥(pSpan P))⁻¹ * y ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyb, inv_mul_cancel]
    have hcenter := Subgroup.mem_center_iff.mp (I.ker_le hk0) ⟨a, le_pSpan hL ha⟩
    have hak : a * (b⁻¹ * (y : G)) = (b⁻¹ * (y : G)) * a := by
      have := congrArg Subtype.val hcenter
      simpa using this
    have hay : a * (y : G) = (y : G) * a := hc a ha y hyL'
    have key : a * b * (b⁻¹ * (y : G)) = b * a * (b⁻¹ * (y : G)) := by
      calc a * b * (b⁻¹ * (y : G)) = a * (y : G) := by group
        _ = (y : G) * a := hay
        _ = b * (b⁻¹ * (y : G)) * a := by rw [mul_inv_cancel_left]
        _ = b * ((b⁻¹ * (y : G)) * a) := by group
        _ = b * (a * (b⁻¹ * (y : G))) := by rw [hak]
        _ = b * a * (b⁻¹ * (y : G)) := by group
    exact mul_right_cancel key
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := hnab L hL
  exact hxy (hall x₀ hx₀ y₀ hy₀)

private theorem e16b6_aeCoverHyp (h : EndHyp Ω) (h9 : Perp9 Ω) {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent (centMembers Ω e) n)
    (hO : classicalInvolutionOddCore ↥(pSpan (centMembers Ω e)) = ⊥) :
    TL4.AECoverHyp I := by
  have hk : IsPGroup 2 ↥I.φ.ker := I.isPGroup_ker hO
  have hPΩ : centMembers Ω e ⊆ Ω := fun _ hL => hL.1
  have hinj := e16b6_label_inj_gen h.thmD.hyp (fun L hL => h.thmD.two L hL) hPΩ I hk
    (fun L hL => (h.isQuatSub_of_mem hL.1).exists_not_commute)
  have hcomm : ∀ (α : Finset (Fin n)) (hα : α.card = 4), ∀ L ∈ centMembers Ω e,
      ∀ L' ∈ centMembers Ω e,
      (L.subgroupOf (pSpan (centMembers Ω e))).map I.φ = AE.memBar α hα true →
      (L'.subgroupOf (pSpan (centMembers Ω e))).map I.φ = AE.memBar α hα false →
      ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := by
    intro α hα L hL L' hL' hl hl'
    have hne : L ≠ L' := by
      rintro rfl
      rw [hl] at hl'
      exact AE.memBar_true_ne_false hn α hα hl'
    refine aeIdent_comm_of_map_comm h.thmD.hyp (fun L hL => h.thmD.two L hL) hPΩ I hk hL hL' hne ?_
    intro x hx y hy
    rw [hl] at hx
    rw [hl'] at hy
    exact memBar_twin_comm α hα true x hx y hy
  exact
    { ker_two := hk
      card := fun L hL => h.card_eq_eight hL.1
      conj_mem := fun L hL x hx => h.toStarHyp.conjSub_mem_centMembers hL hx
      label_inj := hinj
      twin_comm := fun α hα L hL L' hL' hl hl' => hcomm α hα L hL L' hL' hl hl'
      twin_z := fun α hα L hL L' hL' hl hl' u₁ u₂ hu₁ hu₂ =>
        h9 L hL.1 L' hL'.1 (hcomm α hα L hL L' hL' hl hl') u₁ u₂ hu₁ hu₂ }

private theorem e16b6_range (n : ℕ) :
    (AE.aeSub n).map (AE.mkQ n) = TL4.aeModel n := by
  rw [TL4.aeModel_eq, AE.aeBarOver, AE.aeSubOver, inf_eq_left.mpr]
  intro a ha
  rw [Subgroup.mem_comap]
  exact Equiv.Perm.mem_alternatingGroup.mpr ((AE.mem_aeSub).mp ha).2


private theorem e16b6_ne_of_inv {A B : Subgroup G} {a b : G} (hA : IsUniqueInvolution A a)
    (hB : IsUniqueInvolution B b) (hab : a ≠ b) : A ≠ B := by
  rintro rfl
  exact hab (hA.eq hB)

private theorem e16b6_central (x : G) (hx : x ∈ pSpan (centMembers Ω e)) : x * e = e * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun L hL => hL.2) hx)


private theorem e16b6_z_ne_ue (c : Sit16 Ω K K' W z u e g) : z ≠ u * e := by
  intro hzue
  apply c.e_not_mem
  have h1 : e = u * z := by
    calc e = u * (u * e) := by rw [← mul_assoc, c.data.hu2, one_mul]
      _ = u * z := by rw [← hzue]
  rw [h1]
  exact Subgroup.mul_mem _ c.data.hu (Subgroup.mem_sup_left c.twin.isInv.mem)

private theorem e16b6_false_of_uniqueW (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω)
    (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (hKP : K ∈ centMembers Ω e) (hK'P : K' ∈ centMembers Ω e)
    (hJP : conjSub g K ∈ centMembers Ω e)
    (hJinv : IsUniqueInvolution (conjSub g K) (u * e))
    (hW₀ : ∃ W₀ : Subgroup G, WIn (centMembers Ω e) (pSpan (centMembers Ω e)) = {W₀}) :
    False := by
  have he1 : e ≠ 1 := c.data.he1
  have hzK : IsUniqueInvolution K z := c.twin.isInv
  have hzK' : IsUniqueInvolution K' z := c.twin.mem_twin.2
  have hK'Ω : K' ∈ Ω := c.twin.mem_twin.1
  have hJ'inv : IsUniqueInvolution (conjSub g K') (u * e) := by
    have := hzK'.conj g
    rwa [c.data.hgt] at this
  have he_W : e ∈ W := by
    have h1 : e ∈ Subgroup.closure ({e} : Set G) := Subgroup.subset_closure rfl
    rw [c.data.he] at h1
    exact h1.1
  have hue_W : u * e ∈ W := Subgroup.mul_mem _ c.data.huW he_W
  have hzt_W : z * (u * e) ∈ W := Subgroup.mul_mem _ c.data.hzW hue_W
  have hu_ne_ue : z ≠ u * e := by
    intro hzue
    apply c.e_not_mem
    have h1 : e = u * z := by
      calc e = u * (u * e) := by rw [← mul_assoc, c.data.hu2, one_mul]
        _ = u * z := by rw [← hzue]
    rw [h1]
    exact Subgroup.mul_mem _ c.data.hu (Subgroup.mem_sup_left hzK.mem)
  have hue_ne_one : u * e ≠ 1 := hJinv.ne_one
  have hzt_ne_z : z ≠ z * (u * e) := by
    intro hh
    exact hJinv.ne_one (mul_left_cancel (by rw [mul_one]; exact hh.symm))
  have hue_ne_zt : u * e ≠ z * (u * e) := by
    intro hh
    have h1 : 1 * (u * e) = z * (u * e) := by rw [one_mul]; exact hh
    exact hzK.ne_one (mul_right_cancel h1).symm
  obtain ⟨I, hIDS, hIinv⟩ := exists_dSet_zt c h h9
  have hIP : I ∈ centMembers Ω e := c.dSet_subset_centMembers h hIDS
  have hIΩ : I ∈ Ω := hIP.1
  obtain ⟨I', hI'ne, hI'tw⟩ := h.twinSet_pair c.twin hIΩ
  have hI'mem : I' ∈ twinSet Ω I := by
    rw [hI'tw]
    simp
  obtain ⟨zI, hzI, hzI'⟩ := hI'mem.2
  have hzIeq : zI = z * (u * e) := hzI.eq hIinv
  have hI'inv : IsUniqueInvolution I' (z * (u * e)) := hzIeq ▸ hzI'
  have hI'P : I' ∈ centMembers Ω e :=
    c.dSet_subset_centMembers h (h.mem_dSet_of_mem c.data.hW hI'mem.1 hI'inv hzt_W)
  have hJ'P' : conjSub g K' ∈ centMembers Ω e :=
    c.dSet_subset_centMembers h
      (h.mem_dSet_of_mem c.data.hW (h.thmD.hyp.conjInvariant g K' hK'Ω) hJ'inv hue_W)
  have hKN : K ≤ Subgroup.normalizer (W : Set G) :=
    (h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW).2
  have hK'N : K' ≤ Subgroup.normalizer (W : Set G) :=
    (h.mem_dSet_of_mem c.data.hW hK'Ω hzK' c.data.hzW).2
  have hJN : conjSub g K ≤ Subgroup.normalizer (W : Set G) :=
    (h.mem_dSet_of_mem c.data.hW hJP.1 hJinv hue_W).2
  have hJ'N : conjSub g K' ≤ Subgroup.normalizer (W : Set G) :=
    (h.mem_dSet_of_mem c.data.hW (h.thmD.hyp.conjInvariant g K' hK'Ω) hJ'inv hue_W).2
  have hIN : I ≤ Subgroup.normalizer (W : Set G) := (h.mem_dSet_iff.mp hIDS).2
  have hI'N : I' ≤ Subgroup.normalizer (W : Set G) :=
    (h.mem_dSet_of_mem c.data.hW hI'mem.1 hI'inv hzt_W).2
  have hKK' : K ≠ K' := c.twin.ne
  have hcKK' : conjSub g K ≠ conjSub g K' := fun hh => c.twin.ne (conjSub_injective g hh)
  have hII' : I ≠ I' := Ne.symm hI'ne
  have n1 : K ≠ conjSub g K := e16b6_ne_of_inv hzK hJinv hu_ne_ue
  have n2 : K ≠ conjSub g K' := e16b6_ne_of_inv hzK hJ'inv hu_ne_ue
  have n3 : K ≠ I := e16b6_ne_of_inv hzK hIinv (fun hh => hzt_ne_z (by rw [← hh]))
  have n4 : K ≠ I' := e16b6_ne_of_inv hzK hI'inv (fun hh => hzt_ne_z (by rw [← hh]))
  have n5 : K' ≠ conjSub g K := e16b6_ne_of_inv hzK' hJinv hu_ne_ue
  have n6 : K' ≠ conjSub g K' := e16b6_ne_of_inv hzK' hJ'inv hu_ne_ue
  have n7 : K' ≠ I := e16b6_ne_of_inv hzK' hIinv (fun hh => hzt_ne_z (by rw [← hh]))
  have n8 : K' ≠ I' := e16b6_ne_of_inv hzK' hI'inv (fun hh => hzt_ne_z (by rw [← hh]))
  have n9 : conjSub g K ≠ I := e16b6_ne_of_inv hJinv hIinv hue_ne_zt
  have n10 : conjSub g K ≠ I' := e16b6_ne_of_inv hJinv hI'inv hue_ne_zt
  have n11 : conjSub g K' ≠ I := e16b6_ne_of_inv hJ'inv hIinv hue_ne_zt
  have n12 : conjSub g K' ≠ I' := e16b6_ne_of_inv hJ'inv hI'inv hue_ne_zt
  have m1 : I ∉ ({I'} : Set (Subgroup G)) := by
    rw [Set.mem_singleton_iff]
    exact hII'
  have m2 : conjSub g K' ∉ ({I, I'} : Set (Subgroup G)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨n11, n12⟩
  have m3 : conjSub g K ∉ ({conjSub g K', I, I'} : Set (Subgroup G)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hcKK', n9, n10⟩
  have m4 : K' ∉ ({conjSub g K, conjSub g K', I, I'} : Set (Subgroup G)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨n5, n6, n7, n8⟩
  have m5 : K ∉ ({K', conjSub g K, conjSub g K', I, I'} : Set (Subgroup G)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hKK', n1, n2, n3, n4⟩
  have hS6 : ({K, K', conjSub g K, conjSub g K', I, I'} : Set (Subgroup G)).ncard = 6 := by
    rw [Set.ncard_insert_of_notMem m5, Set.ncard_insert_of_notMem m4,
      Set.ncard_insert_of_notMem m3, Set.ncard_insert_of_notMem m2,
      Set.ncard_insert_of_notMem m1, Set.ncard_singleton]
  have hne : centMembers Ω e ≠ {K, K'} := by
    intro hh
    have hmem : conjSub g K ∈ ({K, K'} : Set (Subgroup G)) := hh ▸ hJP
    rcases Set.mem_insert_iff.mp hmem with h1 | h1
    · exact n1 h1.symm
    · exact n5 (Set.mem_singleton_iff.mp h1).symm
  have hsub : ({K, K', conjSub g K, conjSub g K', I, I'} : Set (Subgroup G)) ⊆
      centMembers Ω e := by
    intro R hR
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    rcases hR with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
    · exact hKP
    · exact hK'P
    · exact hJP
    · exact hJ'P'
    · exact hIP
    · exact hI'P
  have h6 := EndHyp.ncard_eq_six_of_uniqueW h h9 he1 c.twin hKP hK'P hne hW₀
  have hcard : (centMembers Ω e).ncard ≤
      ({K, K', conjSub g K, conjSub g K', I, I'} : Set (Subgroup G)).ncard :=
    (h6.trans hS6.symm).le
  have hPeq := Set.eq_of_subset_of_ncard_le hsub hcard
  obtain ⟨R, hRΩ, hRC, hRN⟩ := exists_member_centralizer_not_normalizer c h h9 h13
  have hRP : R ∈ centMembers Ω e := Generic.mem_centMembers.mpr ⟨hRΩ, hRC⟩
  rw [← hPeq] at hRP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hRP
  rcases hRP with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hRN
  · exact hRN hKN
  · exact hRN hK'N
  · exact hRN hJN
  · exact hRN hJ'N
  · exact hRN hIN
  · exact hRN hI'N


private def e16b6_gv (j : Fin 5) : Fin 6 → ZMod 2 := fun i => if i = 0 ∨ i = j.succ then 1 else 0

private theorem e16b6_vec_closure (f : Fin 6 → ZMod 2) (hf : ∑ i, f i = 0) :
    f ∈ AddSubgroup.closure (Set.range e16b6_gv) := by
  have key : ∀ f : Fin 6 → ZMod 2, (∑ i, f i = 0) → ∃ c : Fin 5 → ZMod 2,
      ∀ i, f i = ∑ j, (if c j = 0 then (0 : ZMod 2) else e16b6_gv j i) := by
    decide
  obtain ⟨c, hc⟩ := key f hf
  have hfe : f = ∑ j, (if c j = 0 then (0 : Fin 6 → ZMod 2) else e16b6_gv j) := by
    funext i
    rw [Finset.sum_apply]
    rw [show f i = ∑ j, (if c j = 0 then (0 : ZMod 2) else e16b6_gv j i) from hc i]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> rfl
  rw [hfe]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  split_ifs
  · exact zero_mem _
  · exact AddSubgroup.subset_closure ⟨j, rfl⟩

private theorem e16b6_ofVec_add {n : ℕ} (f f' : Fin n → ZMod 2) :
    AE.Wr.ofVec (f + f') = AE.Wr.ofVec f * AE.Wr.ofVec f' := by
  refine AE.Wr.ext ?_ ?_
  · funext i
    simp [AE.Wr.mul_vec, AE.Wr.ofVec, Equiv.Perm.one_def]
  · simp [AE.Wr.mul_perm, AE.Wr.ofVec]

private theorem e16b6_ofVec_zero {n : ℕ} : AE.Wr.ofVec (0 : Fin n → ZMod 2) = 1 := by
  refine AE.Wr.ext ?_ ?_
  · funext i
    simp [AE.Wr.ofVec, AE.Wr.one_vec]
  · simp [AE.Wr.ofVec, AE.Wr.one_perm]

private theorem e16b6_not_pgroup_A6 :
    ¬ IsPGroup 2 ↥(⊤ : Subgroup (alternatingGroup (Fin 6))) := by
  intro hP
  have hc3A : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    norm_num
  obtain ⟨k, hk⟩ := hP ⟨⟨_, hc3A⟩, Subgroup.mem_top _⟩
  have hk' : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ 2 ^ k = 1 := by
    have := congrArg (fun y : ↥(⊤ : Subgroup (alternatingGroup (Fin 6))) =>
      ((y : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) hk
    simpa using this
  have h3 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
  have hne1 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 ≠ 1 := by decide
  have hord : orderOf (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) = 3 :=
    orderOf_eq_prime h3 hne1
  have hdvd := orderOf_dvd_of_pow_eq_one hk'
  rw [hord] at hdvd
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h32

private theorem e16b6_perm_one_of_normal (N : Subgroup ↥(AE.aeSub 6)) [N.Normal]
    (hN : IsPGroup 2 ↥N) : ∀ w ∈ N, (w : AE.Wr 6).perm = 1 := by
  let pm : ↥(AE.aeSub 6) →* ↥(alternatingGroup (Fin 6)) :=
    MonoidHom.codRestrict ((AE.permHom 6).comp (AE.aeSub 6).subtype) _
      (fun w => Equiv.Perm.mem_alternatingGroup.mpr ((AE.mem_aeSub).mp w.2).2)
  have hsurj : Function.Surjective pm := by
    intro σ
    have hσ : (σ : Equiv.Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := σ.2
    refine ⟨⟨AE.Wr.ofPerm (σ : Equiv.Perm (Fin 6)), ?_⟩, ?_⟩
    · exact AE.mem_aeSub.mpr ⟨by simp [AE.Wr.wsum, AE.Wr.ofPerm],
        Equiv.Perm.mem_alternatingGroup.mp hσ⟩
    · exact Subtype.ext rfl
  haveI : (N.map pm).Normal := Subgroup.Normal.map inferInstance pm hsurj
  have hP : IsPGroup 2 ↥(N.map pm) := hN.map pm
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map pm) with hbot | htop
  · intro w hw
    have hpw : pm w ∈ N.map pm := Subgroup.mem_map_of_mem pm hw
    rw [hbot, Subgroup.mem_bot] at hpw
    exact congrArg (fun y : ↥(alternatingGroup (Fin 6)) => (y : Equiv.Perm (Fin 6))) hpw
  · exact absurd (htop ▸ hP) e16b6_not_pgroup_A6


private theorem e16b6_psi_e (I : AEIdent (centMembers Ω e) 6)
    (ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6))
    (hψ : ∀ x, AE.mkQ 6 (ψ x : AE.Wr 6) = I.φ x) (he : e ∈ pSpan (centMembers Ω e))
    (hφe : I.φ ⟨e, he⟩ = 1) (he1 : e ≠ 1) :
    (ψ ⟨e, he⟩ : AE.Wr 6) = AE.Wr.allOnes 6 := by
  have h1 : AE.mkQ 6 (ψ ⟨e, he⟩ : AE.Wr 6) = 1 := (hψ _).trans hφe
  have h2 : (ψ ⟨e, he⟩ : AE.Wr 6) ∈ AE.piSub 6 := (QuotientGroup.eq_one_iff _).mp h1
  rcases AE.mem_piSub.mp h2 with h3 | h3
  · exfalso
    have h4 : ψ ⟨e, he⟩ = 1 := Subtype.ext h3
    have h5 : (⟨e, he⟩ : ↥(pSpan (centMembers Ω e))) = 1 :=
      ψ.injective (h4.trans (map_one ψ).symm)
    exact he1 (congrArg Subtype.val h5)
  · exact h3

private def e16b6_tau (j : Fin 5) : Fin 6 := if j.succ = 1 then 2 else 1

private theorem e16b6_D_iff (h : EndHyp Ω) (I : AEIdent (centMembers Ω e) 6)
    (ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6))
    (hlab6 : ∀ L ∈ centMembers Ω e, ∀ (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (centMembers Ω e))).map I.φ = AE.memBar α hα b →
        ((L.subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom).map (AE.aeSub 6).subtype =
          AE.memAt α hα b)
    (x : ↥(pSpan (centMembers Ω e))) :
    (x : G) ∈ zGroup Ω ↔ (ψ x : AE.Wr 6).perm = 1 := by
  have hZN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hz2 : IsPGroup 2 ↥(zGroup Ω) := CFSG.pCore_isPGroup.to_le h.zGroup_le_pCore
  have hN2 : IsPGroup 2 ↥((zGroup Ω).subgroupOf (pSpan (centMembers Ω e))) := hz2.comap_subtype
  haveI : ((zGroup Ω).subgroupOf (pSpan (centMembers Ω e))).Normal :=
    Subgroup.Normal.subgroupOf hZN _
  haveI hH0N : (((zGroup Ω).subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ ψ.surjective
  have hH0 : IsPGroup 2 ↥(((zGroup Ω).subgroupOf (pSpan (centMembers Ω e))).map
      ψ.toMonoidHom) := hN2.map ψ.toMonoidHom
  constructor
  · intro hx
    have hxN : x ∈ (zGroup Ω).subgroupOf (pSpan (centMembers Ω e)) :=
      Subgroup.mem_subgroupOf.mpr hx
    have hψH : ψ x ∈ ((zGroup Ω).subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
    exact e16b6_perm_one_of_normal _ hH0 (ψ x) hψH
  · intro hperm
    set H0 := ((zGroup Ω).subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom with hH0def
    have hzOf : ∀ (α : Finset (Fin 6)) (hα : α.card = 4),
        ∃ w ∈ H0, (w : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
      intro α hα
      obtain ⟨R, hR, hlabR⟩ := I.label_surj α hα true
      obtain ⟨zR, hzR⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hR.1
      have hzRX : zR ∈ pSpan (centMembers Ω e) := le_pSpan hR hzR.mem
      have hzRD : zR ∈ zGroup Ω := Subgroup.subset_closure ⟨R, hR.1, hzR⟩
      have hxN : (⟨zR, hzRX⟩ : ↥(pSpan (centMembers Ω e))) ∈
          (zGroup Ω).subgroupOf (pSpan (centMembers Ω e)) := Subgroup.mem_subgroupOf.mpr hzRD
      have hmemR : (ψ ⟨zR, hzRX⟩ : AE.Wr 6) ∈
          ((R.subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom).map (AE.aeSub 6).subtype :=
        Subgroup.mem_map.mpr ⟨ψ ⟨zR, hzRX⟩, Subgroup.mem_map.mpr
          ⟨⟨zR, hzRX⟩, Subgroup.mem_subgroupOf.mpr hzR.mem, rfl⟩, rfl⟩
      rw [hlab6 R hR α hα true hlabR] at hmemR
      have hxx : (⟨zR, hzRX⟩ : ↥(pSpan (centMembers Ω e))) * ⟨zR, hzRX⟩ = 1 :=
        Subtype.ext hzR.sq
      have hsq : (ψ ⟨zR, hzRX⟩ : AE.Wr 6) * (ψ ⟨zR, hzRX⟩ : AE.Wr 6) = 1 := by
        have h1 : ψ ⟨zR, hzRX⟩ * ψ ⟨zR, hzRX⟩ = 1 := by rw [← map_mul, hxx, map_one]
        exact congrArg Subtype.val h1
      rcases AE.eq_of_mem_memAt_mul_self hmemR hsq with h1 | h1
      · exfalso
        have h2 : ψ ⟨zR, hzRX⟩ = 1 := Subtype.ext h1
        have h3 : (⟨zR, hzRX⟩ : ↥(pSpan (centMembers Ω e))) = 1 :=
          ψ.injective (h2.trans (map_one ψ).symm)
        exact hzR.ne_one (congrArg Subtype.val h3)
      · exact ⟨ψ ⟨zR, hzRX⟩, Subgroup.mem_map.mpr ⟨⟨zR, hzRX⟩, hxN, rfl⟩, h1⟩
    have hzvec : ∀ (α : Finset (Fin 6)) (hα : α.card = 4) (i : Fin 6),
        (AE.zOf (AE.emb α hα)).vec i = if i ∈ α then 1 else 0 := by
      intro α hα i
      have hr := AE.range_emb α hα
      rw [AE.zOf_vec_apply]
      by_cases hi : i ∈ α
      · rw [if_pos hi, if_pos (by rw [hr]; exact hi)]
      · rw [if_neg hi, if_neg (by rw [hr]; exact hi)]
    have hcard1 : ∀ j : Fin 5, (Finset.univ \ {j.succ, e16b6_tau j} : Finset (Fin 6)).card = 4 := by
      decide
    have hcard2 : ∀ j : Fin 5, (Finset.univ \ {0, e16b6_tau j} : Finset (Fin 6)).card = 4 := by
      decide
    have hid : ∀ j : Fin 5, ∀ i : Fin 6,
        ((if i ∈ (Finset.univ \ {j.succ, e16b6_tau j} : Finset (Fin 6)) then (1 : ZMod 2) else 0) +
          (if i ∈ (Finset.univ \ {0, e16b6_tau j} : Finset (Fin 6)) then (1 : ZMod 2) else 0)) =
          e16b6_gv j i := by
      decide
    have hgv : ∀ j : Fin 5, ∃ w ∈ H0, (w : AE.Wr 6) = AE.Wr.ofVec (e16b6_gv j) := by
      intro j
      obtain ⟨wα, hwα, eα⟩ := hzOf _ (hcard1 j)
      obtain ⟨wβ, hwβ, eβ⟩ := hzOf _ (hcard2 j)
      refine ⟨wα * wβ, H0.mul_mem hwα hwβ, ?_⟩
      rw [Subgroup.coe_mul, eα, eβ]
      refine AE.Wr.ext ?_ ?_
      · funext i
        simp only [AE.Wr.mul_vec, AE.zOf_perm, Equiv.Perm.one_def, Equiv.refl_symm,
          Equiv.refl_apply, hzvec, AE.Wr.ofVec]
        exact hid j i
      · simp [AE.Wr.mul_perm, AE.zOf_perm, AE.Wr.ofVec]
    have hclos : ∀ f ∈ AddSubgroup.closure (Set.range e16b6_gv),
        ∃ w ∈ H0, (w : AE.Wr 6) = AE.Wr.ofVec f := by
      intro f hf
      induction hf using AddSubgroup.closure_induction with
      | mem f hf =>
        obtain ⟨j, rfl⟩ := hf
        exact hgv j
      | zero => exact ⟨1, H0.one_mem, by rw [e16b6_ofVec_zero]; rfl⟩
      | add a b _ _ ha hb =>
        obtain ⟨w1, hw1, e1⟩ := ha
        obtain ⟨w2, hw2, e2⟩ := hb
        exact ⟨w1 * w2, H0.mul_mem hw1 hw2, by rw [Subgroup.coe_mul, e1, e2, e16b6_ofVec_add]⟩
      | neg a _ ha =>
        obtain ⟨w, hw, e⟩ := ha
        have hmul : AE.Wr.ofVec a * AE.Wr.ofVec (-a) = 1 := by
          rw [← e16b6_ofVec_add, add_neg_cancel, e16b6_ofVec_zero]
        refine ⟨w⁻¹, H0.inv_mem hw, ?_⟩
        rw [Subgroup.coe_inv, e, inv_eq_of_mul_eq_one_right hmul]
    have hw : ∑ i, (ψ x : AE.Wr 6).vec i = 0 := ((AE.mem_aeSub).mp (ψ x).2).1
    obtain ⟨w, hwH, hwe⟩ := hclos _ (e16b6_vec_closure _ hw)
    have hwψ : w = ψ x := by
      apply Subtype.ext
      rw [hwe]
      refine AE.Wr.ext rfl ?_
      rw [hperm]
      rfl
    rw [hwψ] at hwH
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hwH
    have hyx' : y = x := ψ.injective hyx
    rw [hyx'] at hy
    exact Subgroup.mem_subgroupOf.mp hy


private theorem e16b6_phi_e {n : ℕ} (φ : ↥(pSpan (centMembers Ω e)) →* AE.AEQ n)
    (hcen : ∀ m ∈ φ.range, (∀ m' ∈ φ.range, m * m' = m' * m) → m = 1)
    (he : e ∈ pSpan (centMembers Ω e)) : φ ⟨e, he⟩ = 1 := by
  apply hcen _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  intro m' hm'
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hm'
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (e16b6_central (x : G) x.2).symm

theorem exists_equiv_X (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω)
    (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ (I : AEIdent (centMembers Ω e) 6)
      (ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6)),
      TL4.AECoverHyp I ∧ (∀ x, AE.mkQ 6 (ψ x : AE.Wr 6) = I.φ x) ∧
      (∀ L ∈ centMembers Ω e, ∀ (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool),
        (L.subgroupOf (pSpan (centMembers Ω e))).map I.φ = AE.memBar α hα b →
          ((L.subgroupOf (pSpan (centMembers Ω e))).map ψ.toMonoidHom).map (AE.aeSub 6).subtype =
            AE.memAt α hα b) ∧
      (∃ he : e ∈ pSpan (centMembers Ω e), (ψ ⟨e, he⟩ : AE.Wr 6) = AE.Wr.allOnes 6) ∧
      (∀ x : ↥(pSpan (centMembers Ω e)), (x : G) ∈ zGroup Ω ↔ (ψ x : AE.Wr 6).perm = 1) := by
  have he1 : e ≠ 1 := c.data.he1
  obtain ⟨hKP, hK'P, hJP⟩ := e16b6_memb c h
  have hJinv : IsUniqueInvolution (conjSub g K) (u * e) := by
    have := c.twin.isInv.conj g
    rwa [c.data.hgt] at this
  have hez : e ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).2
  have he := e16b6_e_mem c hKP hK'P hJP hJinv
  have hO : classicalInvolutionOddCore ↥(pSpan (centMembers Ω e)) = ⊥ :=
    EndHyp.oddCore_pSpan_centMembers_eq_bot h h9 c.twin h13 hez he1
  rcases EndHyp.centMembers_cases h h9 he1 c.twin hKP hK'P with hpair | ⟨-, hout⟩
  ·
    exfalso
    rw [hpair] at hJP
    rcases Set.mem_insert_iff.mp hJP with h1 | h1
    · exact (e16b6_ne_of_inv c.twin.isInv hJinv (e16b6_z_ne_ue c)) h1.symm
    · exact (e16b6_ne_of_inv c.twin.mem_twin.2 hJinv (e16b6_z_ne_ue c))
        (Set.mem_singleton_iff.mp h1).symm
  · rcases hout with hW₀ | hn | hI
    · obtain ⟨W₀, hW₀⟩ := hW₀
      exact (e16b6_false_of_uniqueW c h h9 h13 hKP hK'P hJP hJinv ⟨W₀, hW₀⟩).elim
    · obtain ⟨n, hn5, hn7, hI⟩ := hn
      obtain ⟨I⟩ := hI
      interval_cases n
      ·
        have hR : I.φ.range = TL4.aeModel 5 := I.range_eq.trans (e16b6_range 5)
        have hcen : ∀ m ∈ I.φ.range, (∀ m' ∈ I.φ.range, m * m' = m' * m) → m = 1 :=
          fun m hm hc => TC.Thin.aeModel_center (by norm_num) m (hR ▸ hm)
            (fun m' hm' => hc m' (hR ▸ hm'))
        exact (e16b6_false_of_odd c h h9 (by norm_num) (by decide) I.φ I.ker_le hcen I.label
          hKP hK'P hJP).elim
      ·
        have hA := e16b6_aeCoverHyp h h9 (by norm_num) I hO
        have hR : I.φ.range = TL4.aeModel 6 := I.range_eq.trans (e16b6_range 6)
        have hcen : ∀ m ∈ I.φ.range, (∀ m' ∈ I.φ.range, m * m' = m' * m) → m = 1 :=
          fun m hm hc => TC.Thin.aeModel_center (by norm_num) m (hR ▸ hm)
            (fun m' hm' => hc m' (hR ▸ hm'))
        have hφe := e16b6_phi_e I.φ hcen he
        obtain ⟨-, hker⟩ := aeCover_ker hA (by norm_num)
        rcases hker with hbot | ⟨ψ, hψ, hlab6⟩
        · exfalso
          have hmem : (⟨e, he⟩ : ↥(pSpan (centMembers Ω e))) ∈ I.φ.ker :=
            MonoidHom.mem_ker.mpr hφe
          rw [hbot, Subgroup.mem_bot] at hmem
          exact he1 (congrArg Subtype.val hmem)
        · exact ⟨I, ψ, hA, hψ, hlab6, ⟨he, e16b6_psi_e I ψ hψ he hφe he1⟩,
            e16b6_D_iff h I ψ hlab6⟩
      ·
        have hR : I.φ.range = TL4.aeModel 7 := I.range_eq.trans (e16b6_range 7)
        have hcen : ∀ m ∈ I.φ.range, (∀ m' ∈ I.φ.range, m * m' = m' * m) → m = 1 :=
          fun m hm hc => TC.Thin.aeModel_center (by norm_num) m (hR ▸ hm)
            (fun m' hm' => hc m' (hR ▸ hm'))
        exact (e16b6_false_of_odd c h h9 (by norm_num) (by decide) I.φ I.ker_le hcen I.label
          hKP hK'P hJP).elim
    ·
      obtain ⟨I⟩ := hI
      have hR : I.φ.range = AE.e64Sub := I.range_eq
      have hcen : ∀ m ∈ I.φ.range, (∀ m' ∈ I.φ.range, m * m' = m' * m) → m = 1 := by
        intro m hm hc
        have hm' : m ∈ AE.e64Sub := by rw [← hR]; exact hm
        have hmem : (⟨m, hm'⟩ : ↥AE.e64Sub) ∈ Subgroup.center ↥AE.e64Sub := by
          rw [Subgroup.mem_center_iff]
          intro g'
          exact Subtype.ext (hc g'.1 (by rw [hR]; exact g'.2)).symm
        rw [PhilipHall.Frame.TwinThinPf.center_e64_eq_bot, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      have hlab : ∀ L ∈ centMembers Ω e, ∃ (α : Finset (Fin 7)) (hα : α.card = 4) (b : Bool),
          (L.subgroupOf (pSpan (centMembers Ω e))).map I.φ = AE.memBar α hα b := by
        intro L hL
        obtain ⟨α, -, hα, b, hl⟩ := I.label L hL
        exact ⟨α, hα, b, hl⟩
      exact (e16b6_false_of_odd c h h9 (by norm_num) (by decide) I.φ I.ker_le hcen hlab
        hKP hK'P hJP).elim

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13

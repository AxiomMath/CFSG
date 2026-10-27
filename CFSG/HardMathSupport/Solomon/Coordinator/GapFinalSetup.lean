module

public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

section Transport

variable {X Y S : Type*} [Group X] [Group Y] [Group S]

theorem hat_of_mulEquiv (e : X ≃* Y)
    (h : commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty ((X ⧸ Subgroup.center X) ≃* S)) :
    commutator Y = ⊤ ∧ Nat.card (Subgroup.center Y) = 3 ∧
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* S) := by
  obtain ⟨hc, hcard, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  · have h1 := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
    rw [commutator]
    exact h1
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hcard]

theorem isHatON_or_isHatSix_of_mulEquiv (e : X ≃* Y) (h : IsHatON X ∨ IsHatSix X) :
    IsHatON Y ∨ IsHatSix Y :=
  h.imp (fun h => hat_of_mulEquiv e h) (fun h => hat_of_mulEquiv e h)

end Transport

section Lift

variable {G : Type*} [Group G] [Finite G]

theorem exists_glaPComponent_lift {L H : Subgroup G} (hHL : H ≤ L) {J' : Subgroup (barOf 3 L)}
    (hJ' : GLAPComponent 3 (barX 3 L H) J') :
    ∃ J : Subgroup G, GLAPComponent 3 H J ∧ barX 3 L J = J' ∧
      Nonempty (barOf 3 J ≃* barOf 3 J') := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set ψ₁ : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hψ₁
  have hker1 : ∀ S : Subgroup ↥L, Nat.Coprime 3 (Nat.card ↥(S ⊓ ψ₁.ker)) := by
    intro S
    have hkr : ψ₁.ker = GLAPPrimeCore 3 ↥L := QuotientGroup.ker_mk' _
    have h1 : Nat.card ↥(S ⊓ ψ₁.ker) ∣ Nat.card ↥(GLAPPrimeCore 3 ↥L) := by
      rw [hkr]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact Nat.Coprime.coprime_dvd_right h1 (coprime_card_gLAPPrimeCore_aux 3 ↥L)
  have hker2 : ∀ S : Subgroup ↥L, Nat.Coprime 3 (Nat.card ↥(S ⊓ L.subtype.ker)) := by
    intro S
    rw [L.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  obtain ⟨K, hK, hKmap⟩ := exists_glaPComponent_map_eq hp ψ₁ (A := H.subgroupOf L) (hker1 _)
    (K' := J') hJ'
  subst hKmap
  have hK2 := glaPComponent_map hp L.subtype (hker2 _) hK
  have hA : (H.subgroupOf L).map L.subtype = H := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHL]
  rw [hA] at hK2
  have hsub : (K.map L.subtype).subgroupOf L = K :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective K
  refine ⟨K.map L.subtype, hK2, ?_, ⟨?_⟩⟩
  · show ((K.map L.subtype).subgroupOf L).map ψ₁ = K.map ψ₁
    rw [hsub]
  · exact (lcEquiv hp L.subtype K (hker2 K)).symm.trans (lcEquiv hp ψ₁ K (hker1 K))

theorem mem_of_mem_barX_of_central {L J : Subgroup G} {b : G} (hbL : b ∈ L) (hb3 : b ^ 3 = 1)
    (hc : ∀ h ∈ L, b * h = h * b)
    (hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨b, hbL⟩ ∈ barX 3 L J) : b ∈ J := by
  obtain ⟨⟨j, hjH⟩, hjJ, hjb⟩ := hmem
  have hjJ' : j ∈ J := Subgroup.mem_subgroupOf.1 hjJ
  have hn : (⟨j, hjH⟩ : ↥L)⁻¹ * ⟨b, hbL⟩ ∈ GLAPPrimeCore 3 ↥L := QuotientGroup.eq.1 hjb
  set n : G := j⁻¹ * b with hn_def
  have hnM : n ∈ GLAPPrimeCoreOf 3 L := by
    rw [mem_gLAPPrimeCoreOf_iff]
    exact ⟨L.mul_mem (L.inv_mem hjH) hbL, hn⟩
  have hbn : b = j * n := by simp [hn_def]
  have hnH : n ∈ L := gLAPPrimeCoreOf_le 3 L hnM
  have hcomm : j * n = n * j := by
    have h1 : b * n = n * b := hc n hnH
    have hj : j = b * n⁻¹ := by rw [hbn]; group
    have h2 : n⁻¹ * b = b * n⁻¹ := by
      calc n⁻¹ * b = n⁻¹ * (b * n) * n⁻¹ := by group
        _ = n⁻¹ * (n * b) * n⁻¹ := by rw [h1]
        _ = b * n⁻¹ := by group
    rw [hj]
    calc b * n⁻¹ * n = b := by group
      _ = n * (b * n⁻¹) := by rw [← h2]; group
  have hord : Nat.Coprime 3 (orderOf n) := by
    have hcop := card_gLAPPrimeCoreOf_coprime 3 L
    refine Nat.Coprime.coprime_dvd_right ?_ hcop
    have := orderOf_dvd_natCard (⟨n, hnM⟩ : ↥(GLAPPrimeCoreOf 3 L))
    rwa [← Subgroup.orderOf_coe] at this
  have hbm : b ^ orderOf n = j ^ orderOf n := by
    have : b ^ orderOf n = (j * n) ^ orderOf n := by rw [← hbn]
    rw [this, (Commute.mul_pow (show Commute j n from hcomm) (orderOf n)), pow_orderOf_eq_one n,
      mul_one]
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hb3) hord.symm)
  rw [← hu, hbm]
  exact J.pow_mem (J.pow_mem hjJ' _) _

end Lift

theorem gapFinalSetup_of_layer (hR1 : GapFinalLayerON) (h183 : Lemma512Ns.Input18_3) :
    GapFinalSetup := by
  intro G _ _ m hS h4 B' hB b hb hb1 L hL hON hbL hBN a haB haZ
  have hBe : CFSG.Open.IsElemAbelian 3 B' := hB.1.1
  have hb3 : b ^ 3 = 1 := hBe.2 b hb
  have ha3 : a ^ 3 = 1 := hBe.2 a haB
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Subgroup.one_mem _)
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hab : b * a = a * b := by
    have := hBe.1.is_comm.comm ⟨b, hb⟩ ⟨a, haB⟩
    simpa using congrArg Subtype.val this
  have hLb : L ≤ Cen b := hL.1
  have hbZ : ∀ l ∈ L, l * b = b * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLb hl)
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hBN haB
  have hα3 : (barAut 3 L ⟨a, haN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext ha3
    rw [this, map_one]
  have hbcen : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨b, hbL⟩ : barOf 3 L) ∈
      Subgroup.center (barOf 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hbZ l l.2)
  obtain ⟨hex, hall⟩ := hR1 (barOf 3 L) hON (barAut 3 L ⟨a, haN⟩) hα3
  obtain ⟨J', hJ'⟩ := hex
  have hfix : Lemma510Ns.fixSub (barAut 3 L ⟨a, haN⟩) = barX 3 L (L ⊓ Cen a) :=
    fixedSub_barAut_eq ha3 haN
  rw [hfix] at hJ'
  obtain ⟨hZJ, hJty⟩ := hall J' (by rw [hfix]; exact hJ')
  obtain ⟨J₀, hJ0c, hJ0bar, ⟨e⟩⟩ := exists_glaPComponent_lift (inf_le_left : L ⊓ Cen a ≤ L) hJ'
  have hbJ0 : b ∈ J₀ := by
    refine mem_of_mem_barX_of_central hbL hb3 (fun h hh => (hbZ h hh).symm) ?_
    rw [hJ0bar]
    exact hZJ hbcen
  have hLle : L ≤ GLAPLayer 3 (Cen b) := le_sSup hL
  have hLayer_le : ∀ X : Subgroup G, GLAPLayer 3 X ≤ X := fun X => sSup_le fun K hK => hK.1
  have hLsn : CFSG.Open.IsSubnormal L (GLAPLayer 3 (Cen b)) :=
    isSubnormal_of_le_of_le hL.2.1 hLle (hLayer_le _)
  have hHsnM : CFSG.Open.IsSubnormal (L ⊓ Cen a) (GLAPLayer 3 (Cen b) ⊓ Cen a) :=
    isSubnormal_inf hLsn (Cen a)
  have hJ0snM : CFSG.Open.IsSubnormal J₀ (GLAPLayer 3 (Cen b) ⊓ Cen a) :=
    isSubnormal_trans' hJ0c.2.1 hHsnM
  have hJ0M : GLAPComponent 3 (GLAPLayer 3 (Cen b) ⊓ Cen a) J₀ :=
    glaPComponent_up Nat.prime_three hJ0c (inf_le_inf_right _ hLle) hJ0snM
  have hJ0Mle : J₀ ≤ GLAPLayer 3 (GLAPLayer 3 (Cen b) ⊓ Cen a) := le_sSup hJ0M
  have hJ0Ml : GLAPComponent 3 (GLAPLayer 3 (GLAPLayer 3 (Cen b) ⊓ Cen a)) J₀ :=
    glaPComponent_down Nat.prime_three hJ0M hJ0Mle (hLayer_le _)
  have := hS.simple
  obtain ⟨hdich, -⟩ := h183 G hS.nonabelian hS.kProper b a hbo hao hab J₀ hJ0Ml
  have hJK : J₀ ≤ conjHull a J₀ := by
    have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Cen a)) => GLBConj g J₀) 1 (one_mem _)
    rwa [gLBConj_one] at this
  obtain ⟨L₁, hL₁, hK⟩ : ∃ L₁ : Subgroup G, GLAPComponent 3 (Cen a) L₁ ∧ conjHull a J₀ = L₁ := by
    rcases hdich with ⟨L₁, hL₁, hK, -⟩ | ⟨L₁, L₂, L₃, h₁, h₂, h₃, h12, -, h31, hu1, -, -, hK⟩
    · exact ⟨L₁, hL₁, hK⟩
    · exact (not_diag hbJ0 (hK ▸ hJK) h₁ h₂ h₃ h12 h31 hu1).elim
  refine ⟨J₀, hJ0c, ?_, hbJ0, ?_⟩
  · exact isHatON_or_isHatSix_of_mulEquiv e.symm hJty
  · rw [hK]
    exact hL₁

end CFSG.HardMathSupport.Solomon.Coordinator

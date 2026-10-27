module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lift

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

variable {G : Type} [Group G] [Finite G] {r : ℕ}

section Quot

variable {N : Subgroup G} [N.Normal] {Λ : Set (Subgroup G)}

theorem TypeRFam.exists_conj_of_map_eq (h : TypeRFam r Λ) (hN : Odd (Nat.card N))
    {K L : Subgroup G} (hK : K ∈ Λ) (hL : L ∈ Λ)
    (heq : K.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, L = conjSub n K := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK
  obtain ⟨y, hy⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL
  have h1 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz
  have h2 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN L) hy
  rw [heq] at h1
  obtain ⟨n, hn, hny⟩ := exists_conj_eq_of_map_eq hN hy.sq hz.sq (h2.eq h1)
  refine ⟨n, hn, h.noTwins _ (h.hyp.conjInvariant n K hK) L ⟨hL, y, ?_, hy⟩⟩
  rw [← hny]
  exact hz.conj n

theorem TypeRFam.exists_conj_omegaNbr_of_map (h : TypeRFam r Λ) (hN : Odd (Nat.card N))
    {K J : Subgroup G} (hK : K ∈ Λ) (hJ : J ∈ Λ)
    (hnbr : J.map (QuotientGroup.mk' N) ∈
      omegaNbr (Asc77.quotFamily Λ N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaNbr Λ (conjSub n K) := by
  have hΩ' := (h.quotFamily hN).hyp
  obtain ⟨-, hne, Rb, hRb, hRbJ, hRbN⟩ := hnbr
  obtain ⟨J₁, hJ₁, hRbsyl⟩ := exists_isSylow2In_of_mem_RSet hRb
  have h8 : 8 ≤ Nat.card Rb := Sec6Gen.eight_le_of_mem_RSet hΩ' hRb
  have hJ₁eq : J₁ = J.map (QuotientGroup.mk' N) :=
    Sec6Gen.eq_of_le_of_le hΩ' hJ₁ (map_mem_quotFamily hJ) hRbsyl.2.1 (by omega) hRbsyl.1 hRbJ
  rw [hJ₁eq] at hRbsyl
  obtain ⟨R₀, hR₀, hR₀J, -⟩ :=
    exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  obtain ⟨xb, hxbJ, hconj⟩ := exists_conjSub_eq_of_isSylow2In (isSylow2In_map_mk hN hR₀J) hRbsyl
  obtain ⟨x, hxJ, hx⟩ := Subgroup.mem_map.mp hxbJ
  have hRΩ : conjSub x R₀ ∈ RSet Λ := RSet.conj h.hyp.conjInvariant hR₀ x
  have hRJ : conjSub x R₀ ≤ J := by
    have := conjSub_mono (n := x) hR₀J.1
    rwa [conjSub_eq_self_of_mem hxJ] at this
  have hRmap : (conjSub x R₀).map (QuotientGroup.mk' N) = Rb := by
    rw [AscQuot.map_conjSub, hx]
    exact hconj
  have hR2 : IsPGroup 2 (conjSub x R₀) := isPGroup_conjSub x hR₀J.2.1
  have hperm : ∀ v ∈ conjSub x R₀, ∃ n ∈ N, conjSub v K = conjSub n K := by
    intro v hv
    have hvN : QuotientGroup.mk' N v ∈ Subgroup.normalizer
        ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
      hRbN (hRmap ▸ Subgroup.mem_map_of_mem _ hv)
    have himg : K.map (QuotientGroup.mk' N) = (conjSub v K).map (QuotientGroup.mk' N) := by
      rw [AscQuot.map_conjSub]
      exact (conjSub_eq_of_mem_normalizer hvN).symm
    exact h.exists_conj_of_map_eq hN hK (h.hyp.conjInvariant v K hK) himg
  obtain ⟨n, hn, hRn⟩ := exists_conj_normalizer_of_perm hN K hR2 hperm
  refine ⟨n, hn, hJ, ?_, conjSub x R₀, hRΩ, hRJ, hRn⟩
  intro hJK
  apply hne
  rw [hJK, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
    (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]

end Quot

section Layer

variable {Ω : Set (Subgroup G)} {x : G}

theorem exists_conj_omegaNbr_of_secImg (h : TypeRFam r Ω) {L M : Subgroup G}
    (hL : XMem Ω x L) (hM : XMem Ω x M)
    (hnbr : secImg Ω x M ∈ omegaNbr (secFam Ω x) (secImg Ω x L)) :
    ∃ ν : ↥(layerY Ω x), ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) ∧
      M ∈ omegaNbr Ω (conjSub (ν : G) L) := by
  obtain ⟨n, hn, hpair⟩ := (h.pairFam (x := x)).exists_conj_omegaNbr_of_map
    odd_natCard_oddCore_layerY (subgroupOf_mem_pairFam hL) (subgroupOf_mem_pairFam hM) hnbr
  refine ⟨n, hn, ?_⟩
  have hnx : (n : G) ∈ Subgroup.centralizer ({x} : Set G) := layerY_le_centralizer n.2
  have hLn : XMem Ω x (conjSub (n : G) L) := XMem.conj' h.hyp.conjInvariant hL hnx
  rw [conjSub_subgroupOf, conjSub_coreAt x hnx] at hpair
  obtain ⟨-, hne, P', hP', hPM, hPN⟩ := hpair
  obtain ⟨C, hC, hCY, hPC⟩ := exists_isSylow2In_of_mem_RSet_restrict hP'
  obtain ⟨L₁, hL₁, rfl⟩ := hC
  refine ⟨hM.1, fun e => hne (by rw [e]), P'.map (layerY Ω x).subtype,
    mem_RSet_of_isSylow2In hL₁.1 ((isSylow2In_coreAt_iff hL₁).mp hPC).1, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact coreAt_le x M (Subgroup.mem_subgroupOf.mp (hPM hu))
  · obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hLn.1
    have hzC := isUniqueInvolution_coreAt h hLn hz
    rintro _ ⟨u, hu, rfl⟩
    have hu1 : (u : G) ∈ Subgroup.normalizer (coreAt x (conjSub (n : G) L) : Set G) :=
      (mem_normalizer_subgroupOf_iff (coreAt_le_layerY hLn)).mpr (hPN hu)
    have hcz : (u : G) * z * (u : G)⁻¹ = z := hzC.conj_eq (mem_normalizer_iff_conjSub_eq.mp hu1)
    refine h.tight _ hLn.1 z hz (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    calc (u : G) * z = ((u : G) * z * (u : G)⁻¹) * (u : G) := by group
      _ = z * (u : G) := by rw [hcz]

theorem exists_conj_mem_dComp_of_conn (h : TypeRFam r Ω) {K : Subgroup G} (hK : XMem Ω x K)
    (hconn : DConnected (secFam Ω x)) {L : Subgroup G} (hL : XMem Ω x L) :
    ∃ ν : ↥(layerY Ω x), ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) ∧
      conjSub (ν : G) L ∈ dComp Ω K := by
  have hcl := h.hyp.conjInvariant
  have key : ∀ b, Relation.ReflTransGen
      (fun M N : Subgroup (SecQuot Ω x) => N ∈ secFam Ω x ∧ dAdj (secFam Ω x) M N)
      (secImg Ω x K) b →
      b ∈ secFam Ω x ∧ ∀ M, XMem Ω x M → secImg Ω x M = b →
        ∃ ν : ↥(layerY Ω x), ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) ∧
          conjSub (ν : G) M ∈ dComp Ω K := by
    intro b hb
    induction hb with
    | refl =>
      refine ⟨secImg_mem hK, fun M hM hMb => ?_⟩
      obtain ⟨ν, hν, hνK⟩ := exists_conj_of_secImg_eq h hK hM hMb.symm
      refine ⟨ν⁻¹, (classicalInvolutionOddCore _).inv_mem hν, ?_⟩
      rw [hνK, Subgroup.coe_inv, conjSub_inv_conjSub]
      exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      obtain ⟨hbΦ, hPb⟩ := ih
      obtain ⟨hcΦ, hadj⟩ := hbc
      refine ⟨hcΦ, fun M hM hMc => ?_⟩
      obtain ⟨M₁, hM₁, rfl⟩ := mem_secFam_iff.mp hbΦ
      obtain ⟨ν₁, hν₁, hM₂⟩ := hPb M₁ hM₁ rfl
      have hν₁x : (ν₁ : G) ∈ Subgroup.centralizer ({x} : Set G) :=
        layerY_le_centralizer ν₁.2
      have hM₂X : XMem Ω x (conjSub (ν₁ : G) M₁) := XMem.conj' hcl hM₁ hν₁x
      have hM₂b : secImg Ω x (conjSub (ν₁ : G) M₁) = secImg Ω x M₁ := secImg_conj_of_mem hν₁ M₁
      rcases hadj with h1 | h2
      · rw [← hM₂b, ← hMc] at h1
        obtain ⟨m, hm, hmn⟩ := exists_conj_omegaNbr_of_secImg h hM₂X hM h1
        refine ⟨m⁻¹, (classicalInvolutionOddCore _).inv_mem hm, ?_⟩
        have h3 := omegaNbr_conj hcl hmn ((m : G)⁻¹)
        rw [conjSub_inv_conjSub] at h3
        rw [Subgroup.coe_inv]
        exact Relation.ReflTransGen.tail hM₂ ⟨hcl _ M hM.1, Or.inl h3⟩
      · rw [← hM₂b, ← hMc] at h2
        obtain ⟨m, hm, hmn⟩ := exists_conj_omegaNbr_of_secImg h hM hM₂X h2
        exact ⟨m, hm, Relation.ReflTransGen.tail hM₂ ⟨hcl _ M hM.1, Or.inr hmn⟩⟩
  exact (key _ (hconn _ (secImg_mem hK) _ (secImg_mem hL))).2 L hL rfl

end Layer

end CFSG.ClassicalInvolution.Q3.TL4

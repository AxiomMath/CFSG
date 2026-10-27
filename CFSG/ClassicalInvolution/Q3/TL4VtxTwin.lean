module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.RecogE4
public import CFSG.ClassicalInvolution.Q3.TL4VtxDich
public import CFSG.ClassicalInvolution.Q3.TL4VtxFamB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace Vtx

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {n : ℕ}

theorem twin_outcome (h4 : Thm4RBelow 3 n) (htw : PhilipHall.Frame.Thm1RTwinLiftSetBelow n)
    (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n)
    {K : Subgroup Q} (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z) {L : Subgroup Q}
    (hL : IsComponent L) (hm : ∃ y ∈ L, z * y ≠ y * z) (htf : ¬ TwinFreeAt Φ K z L) :
    PhilipHall.Frame.TwinE4 ↥(orbGrp Φ K) ∨ TightHasLift K z := by
  have hcl := h.hyp.conjInvariant
  obtain ⟨S', hd', hc'⟩ := tightCls_orbGrp h4 h hO hn hK hz
  have hLn := normal_subgroupOf_orbGrp h4 h hO hn hK hz hL hm
  have hNc := centralizer_subgroupOf_le_center h4 h hO hn hK hz hL hm
  have hN2 := isPGroup_centralizer_subgroupOf h4 h hO hn hK hz hL hm
  obtain ⟨y₀, hy₀, hne₀⟩ := hm
  have hLX : L ≤ orbGrp Φ K := le_orbGrp_of_moves hcl hK hL ⟨z, hz.mem, y₀, hy₀, hne₀⟩
  have hKX : K ≤ orbGrp Φ K := le_orbGrp K
  set N := Subgroup.centralizer
    ((L.subgroupOf (orbGrp Φ K) : Subgroup ↥(orbGrp Φ K)) : Set ↥(orbGrp Φ K)) with hNdef
  have : N.Normal := Subgroup.normal_centralizer
  have hmemN : ∀ w : ↥(orbGrp Φ K), (∀ l ∈ L, (w : Q) * l = l * w) → w ∈ N := by
    intro w hw
    rw [hNdef, Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subtype.ext (hw l (Subgroup.mem_subgroupOf.mp hl)).symm
  have htN : (⟨z, hKX hz.mem⟩ : ↥(orbGrp Φ K)) ∉ N := by
    intro hzN
    exact hne₀ (congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hzN ⟨y₀, hLX hy₀⟩ (Subgroup.mem_subgroupOf.mpr hy₀))).symm
  simp only [TwinFreeAt, not_forall] at htf
  obtain ⟨g, hg, hgL, hgz⟩ := htf
  set w : ↥(orbGrp Φ K) := ⟨g, hg⟩ * ⟨z, hKX hz.mem⟩ * ⟨g, hg⟩⁻¹ * ⟨z, hKX hz.mem⟩⁻¹ with hwdef
  have hwN : w ∈ N := hmemN w hgL
  have hw1 : w ≠ 1 := by
    intro h1
    apply hgz
    have h2 : (w : Q) = 1 := congrArg Subtype.val h1
    simp only [hwdef, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    calc g * z * g⁻¹ = g * z * g⁻¹ * z⁻¹ * z := by group
      _ = z := by rw [h2, one_mul]
  have hy : (⟨g, hg⟩ : ↥(orbGrp Φ K)) * ⟨z, hKX hz.mem⟩ * ⟨g, hg⟩⁻¹ =
      ⟨z, hKX hz.mem⟩ * w := by
    have hwz : w * ⟨z, hKX hz.mem⟩ = ⟨z, hKX hz.mem⟩ * w :=
      (Subgroup.mem_center_iff.mp (hNc hwN) _).symm
    calc (⟨g, hg⟩ : ↥(orbGrp Φ K)) * ⟨z, hKX hz.mem⟩ * ⟨g, hg⟩⁻¹ =
        w * ⟨z, hKX hz.mem⟩ := by rw [hwdef]; group
      _ = ⟨z, hKX hz.mem⟩ * w := hwz
  have hq := PhilipHall.QuaternionBridge.q8Quot_of_twin hd' hc' hNc hN2 htN hwN hw1 hy
  have hA := PhilipHall.QuaternionBridge.aEmpty_map' hd' hc'.1 hNc hN2 htN
  have hcard : Nat.card (↥(orbGrp Φ K) ⧸ N) < n :=
    lt_of_lt_of_le hq.card_lt ((Subgroup.card_le_card_group _).trans hn.le)
  rcases htw.hasLift hcard hq.datum hq.cls.1 hq.cls.2.1 hq.cls.2.2 hq.hyp hA hq.twin with
    hE2 | hE4 | hlift
  · exact absurd (TwistQ.inO2_of hN2 hE2)
      (not_tightInO2_orbGrp hcl hK hz hL ⟨y₀, hy₀, hne₀⟩)
  · obtain ⟨Q', _, f, hfs, hf2, hQ'⟩ := hE4
    refine Or.inl ⟨Q', inferInstance, f.comp (QuotientGroup.mk' N),
      hfs.comp (QuotientGroup.mk'_surjective N), ?_, hQ'⟩
    rw [← MonoidHom.comap_ker]
    exact hf2.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact hN2)
  · right
    have hgood := PhilipHall.QuaternionBridge.good_of_hasLift_twin hd' hNc hN2 htN hlift
    obtain ⟨L', hKL', hL'⟩ := tightHasLift_of_good hd' hgood
    refine ⟨L'.map (orbGrp Φ K).subtype, ?_,
      isClassicalMember3_map_subnormal (isSubnormal_orbGrp hcl hK) hL'⟩
    have hcore : tightCore (K.subgroupOf (orbGrp Φ K)) = K.subgroupOf (orbGrp Φ K) := by
      rw [tightCore_subgroupOf ((tightCore_le K).trans hKX)]
      congr 1
      exact h.closure_twoElts hK
    rw [hcore] at hKL'
    have h1 := Subgroup.map_mono (f := (orbGrp Φ K).subtype) hKL'
    rw [Subgroup.map_subgroupOf_eq_of_le hKX] at h1
    exact (tightCore_le K).trans h1

omit [Finite Q] in
theorem not_isPGroup_two_of_isComponent [Finite Q] {L : Subgroup Q} (hL : IsComponent L) :
    ¬ IsPGroup 2 ↥L := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hs, a, b, hab⟩ := hL.1
  have h2' : IsPGroup 2 (↥L ⧸ Subgroup.center ↥L) :=
    h2.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hZ := h2'.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ Subgroup.center ↥L))
    with h | h
  · exact (Subgroup.nontrivial_iff_ne_bot _).mp hZ h
  · exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem exLie_of_twinE4 {X L : Subgroup Q} (hLX : L ≤ X) (hLn : (L.subgroupOf X).Normal)
    (hL : IsComponent L) (hE4 : PhilipHall.Frame.TwinE4 ↥X) :
    PhilipHall.QuaternionBridge.ExLie (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨Q', _, f, hfs, hf2, hQ'⟩ := hE4
  have : Finite Q' := Finite.of_surjective f hfs
  have hsimple : IsSimpleGroup Q' := by
    rcases hQ' with hQ | hQ
    · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Q' 3 2 1
          hcl
      all_goals exact absurd h0 (by norm_num)
    · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
          Q' 4 2 1 hcl).2
      all_goals exact absurd h0 (by norm_num)
  let θ : ↥L →* Q' := f.comp (Subgroup.inclusion hLX)
  have hθn : θ.range.Normal := by
    have e : θ.range = (L.subgroupOf X).map f := by
      ext q
      constructor
      · rintro ⟨l, rfl⟩
        exact ⟨Subgroup.inclusion hLX l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    rw [e]
    exact hLn.map f hfs
  have hθs : Function.Surjective θ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal θ.range with hb | ht
    · exfalso
      have hle : L.subgroupOf X ≤ f.ker := fun x hx => by
        have hθx : θ ⟨x, Subgroup.mem_subgroupOf.mp hx⟩ ∈ θ.range := ⟨_, rfl⟩
        rw [hb, Subgroup.mem_bot] at hθx
        exact hθx
      exact not_isPGroup_two_of_isComponent hL
        ((hf2.to_le hle).of_equiv (Subgroup.subgroupOfEquivOfLe hLX))
    · exact MonoidHom.range_eq_top.mp ht
  have hkerZ : θ.ker ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL.1 θ.normal_ker with ht | hle
    · exfalso
      obtain ⟨a, b, hab⟩ := @exists_pair_ne Q' hsimple.toNontrivial
      obtain ⟨a', rfl⟩ := hθs a
      obtain ⟨b', rfl⟩ := hθs b
      have ha : θ a' = 1 := (ht ▸ Subgroup.mem_top a' : a' ∈ θ.ker)
      have hb : θ b' = 1 := (ht ▸ Subgroup.mem_top b' : b' ∈ θ.ker)
      exact hab (ha.trans hb.symm)
    · exact hle
  have hZ : Subgroup.center Q' = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q') with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hL.1
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      have hc : θ (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
        have h1 := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (θ b')) (θ a')
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      have h2 := hkerZ hc
      apply hab
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have e : (a' * b')⁻¹ * (b' * a') =
          (b'⁻¹ * a'⁻¹) * (a' * b' * a'⁻¹ * b'⁻¹)⁻¹ * (b'⁻¹ * a'⁻¹)⁻¹ := by group
      rw [e]
      exact (inferInstance : (Subgroup.center ↥L).Normal).conj_mem _
        (Subgroup.inv_mem _ h2) (b'⁻¹ * a'⁻¹)
  have hker : θ.ker = Subgroup.center ↥L := by
    refine le_antisymm hkerZ fun c hc => ?_
    rw [MonoidHom.mem_ker]
    have hcZ : θ c ∈ Subgroup.center Q' := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨l, rfl⟩ := hθs q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc l]
    rwa [hZ, Subgroup.mem_bot] at hcZ
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* Q' :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθs)
  rcases hQ' with hQ | hQ
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hQ)
  · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hQ)

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4

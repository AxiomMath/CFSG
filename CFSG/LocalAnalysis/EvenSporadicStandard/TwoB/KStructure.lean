module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Centralizer

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22

variable {G : Type} [Group G]

theorem le_O2In {H V : Subgroup G} (hVH : V ≤ H) (hn : (V.subgroupOf H).Normal)
    (hp : IsPGroup 2 V) : V ≤ O2In H := by
  intro x hx
  refine ⟨⟨x, hVH hx⟩, ?_, rfl⟩
  have hp' : IsPGroup 2 (V.subgroupOf H) := hp.of_equiv (subgroupOfEquivOfLe hVH).symm
  have hmem : V.subgroupOf H ∈ CFSG.normalPSubgroups 2 ↥H := ⟨hn, hp'⟩
  exact (le_sSup hmem : V.subgroupOf H ≤ CFSG.pCore 2 ↥H) (mem_subgroupOf.2 hx)

theorem isPGroup_O2In (H : Subgroup G) : IsPGroup 2 (O2In H) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).of_equiv
    (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)

theorem normal_subgroupOf_O2In (H : Subgroup G) : ((O2In H).subgroupOf H).Normal := by
  have : (O2In H).subgroupOf H = CFSG.pCore 2 ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [this]
  exact CFSG.pCore_normal

theorem mem_pCore_iff_mem_O2In {H : Subgroup G} (x : ↥H) :
    x ∈ CFSG.pCore 2 ↥H ↔ (x : G) ∈ O2In H := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

section KStructure

variable {L S0 : Subgroup G} {t z : G}

theorem centPair_eq_sup (hz : z ∈ L) (htL : ∀ l ∈ L, l * t = t * l)
    (hS0 : S0 ≤ centralizer (L : Set G)) (hS0c : ∀ a ∈ S0, ∀ b ∈ S0, a * b = b * a)
    (htS0 : t ∈ S0) (hC : centralizer ({t} : Set G) = L ⊔ S0) :
    centPair z t = (L ⊓ centZ z) ⊔ S0 := by
  have hSz : ∀ s ∈ S0, z * s = s * z := fun s hs => mem_centralizer_iff.1 (hS0 hs) z hz
  apply le_antisymm
  · intro x hx
    rw [mem_centralizer_iff] at hx
    have hxz : z * x = x * z := hx z (mem_sup_left (mem_zpowers z))
    have hxt : t * x = x * t := hx t (mem_sup_right (mem_zpowers t))
    have hxC : x ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hxt.symm
    rw [hC] at hxC
    obtain ⟨l, hl, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hS0 hxC
    have hlz : l * z = z * l := by
      have h1 : z * l * s = l * z * s := by
        calc z * l * s = z * (l * s) := by rw [mul_assoc]
          _ = l * s * z := hxz
          _ = l * (s * z) := by rw [mul_assoc]
          _ = l * (z * s) := by rw [hSz s hs]
          _ = l * z * s := by rw [mul_assoc]
      exact (mul_right_cancel h1).symm
    exact Subgroup.mul_mem_sup ⟨hl, mem_centralizer_singleton_iff.2 hlz⟩ hs
  · refine sup_le ?_ ?_
    · rintro g ⟨hgL, hgz⟩
      rw [mem_centralizer_iff]
      intro y hy
      have hle : pair z t ≤ centralizer ({g} : Set G) := by
        refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
        · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hgz).symm
        · exact mem_centralizer_singleton_iff.2 (htL g hgL).symm
      exact mem_centralizer_singleton_iff.1 (hle hy)
    · intro s hs
      rw [mem_centralizer_iff]
      intro y hy
      have hle : pair z t ≤ centralizer ({s} : Set G) := by
        refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
        · exact mem_centralizer_singleton_iff.2 (hSz s hs)
        · exact mem_centralizer_singleton_iff.2 (hS0c t htS0 s hs)
      exact mem_centralizer_singleton_iff.1 (hle hy)

theorem O2In_centPair_eq (hz : z ∈ L) (htL : ∀ l ∈ L, l * t = t * l)
    (hS0 : S0 ≤ centralizer (L : Set G)) (hS0c : ∀ a ∈ S0, ∀ b ∈ S0, a * b = b * a)
    (htS0 : t ∈ S0) (hC : centralizer ({t} : Set G) = L ⊔ S0) (hS02 : IsPGroup 2 S0) :
    O2In (centPair z t) = O2In (L ⊓ centZ z) ⊔ S0 ∧
      O2In (L ⊓ centZ z) ≤ O2In (centPair z t) ∧
      O2In (centPair z t) ⊓ (L ⊓ centZ z) ≤ O2In (L ⊓ centZ z) := by
  have hK := centPair_eq_sup hz htL hS0 hS0c htS0 hC
  have hC0L : ((L ⊓ centZ z : Subgroup G) : Set G) ⊆ (L : Set G) := fun x hx => hx.1
  have hS0C0 : S0 ≤ centralizer ((L ⊓ centZ z : Subgroup G) : Set G) :=
    hS0.trans (Subgroup.centralizer_le hC0L)
  have hdec : ∀ k ∈ centPair z t, ∃ c ∈ L ⊓ centZ z, ∃ s ∈ S0, k = c * s := fun k hk =>
    exists_mul_of_mem_sup_of_le_centralizer hS0C0 (hK ▸ hk)
  have hC0K : L ⊓ centZ z ≤ centPair z t := hK ▸ le_sup_left
  have hS0K : S0 ≤ centPair z t := hK ▸ le_sup_right
  have hO2C0 : O2In (L ⊓ centZ z) ≤ L ⊓ centZ z := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hO2K : O2In (centPair z t) ≤ centPair z t := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcommS : ∀ s ∈ S0, ∀ n ∈ L, s * n = n * s := fun s hs n hn =>
    (mem_centralizer_iff.1 (hS0 hs) n hn).symm
  have hS0n : (S0.subgroupOf (centPair z t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨c, hc, s, hs, hg⟩ := hdec g g.2
    have hcn : (n : G) * c = c * n := hcommS n hn c hc.1
    have hsn : s * n = n * s := hS0c s hs n hn
    have hcs : (c * s) * n = n * (c * s) := by
      calc (c * s) * n = c * (s * n) := by rw [mul_assoc]
        _ = c * (n * s) := by rw [hsn]
        _ = (c * n) * s := by rw [mul_assoc]
        _ = (n * c) * s := by rw [hcn]
        _ = n * (c * s) := by rw [mul_assoc]
    have : (g : G) * n * (g : G)⁻¹ = n := by
      rw [hg, hcs, mul_assoc, mul_inv_cancel, mul_one]
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ S0
    rw [this]
    exact hn
  have hS0U : S0 ≤ O2In (centPair z t) := le_O2In hS0K hS0n hS02
  have hN0n : ((O2In (L ⊓ centZ z)).subgroupOf (centPair z t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨c, hc, s, hs, hg⟩ := hdec g g.2
    have hnC0 : (n : G) ∈ L ⊓ centZ z := hO2C0 hn
    have hsn : s * n = n * s := hcommS s hs n hnC0.1
    have hsn' : s * n * s⁻¹ = n := by rw [hsn, mul_assoc, mul_inv_cancel, mul_one]
    have hconj : (g : G) * n * (g : G)⁻¹ = c * n * c⁻¹ := by
      rw [hg]
      calc c * s * n * (c * s)⁻¹ = c * (s * n * s⁻¹) * c⁻¹ := by group
        _ = c * n * c⁻¹ := by rw [hsn']
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ O2In (L ⊓ centZ z)
    rw [hconj]
    have := (normal_subgroupOf_O2In (L ⊓ centZ z)).conj_mem ⟨n, hnC0⟩ hn ⟨c, hc⟩
    exact this
  have hN0U : O2In (L ⊓ centZ z) ≤ O2In (centPair z t) :=
    le_O2In (hO2C0.trans hC0K) hN0n (isPGroup_O2In _)
  have hinf : O2In (centPair z t) ⊓ (L ⊓ centZ z) ≤ O2In (L ⊓ centZ z) := by
    refine le_O2In inf_le_right ?_ ((isPGroup_O2In _).to_le inf_le_left)
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hgK : (g : G) ∈ centPair z t := hC0K g.2
    have h1 : (g : G) * n * (g : G)⁻¹ ∈ O2In (centPair z t) := by
      have := (normal_subgroupOf_O2In (centPair z t)).conj_mem
        ⟨n, hC0K n.2⟩ (by rw [mem_subgroupOf]; exact hn.1) ⟨g, hgK⟩
      exact this
    exact ⟨h1, (L ⊓ centZ z).mul_mem ((L ⊓ centZ z).mul_mem g.2 n.2) ((L ⊓ centZ z).inv_mem g.2)⟩
  refine ⟨le_antisymm ?_ (sup_le hN0U hS0U), hN0U, hinf⟩
  intro x hx
  obtain ⟨c, hc, s, hs, rfl⟩ := hdec x (hO2K hx)
  have hcU : c ∈ O2In (centPair z t) := by
    have := (O2In (centPair z t)).mul_mem hx ((O2In (centPair z t)).inv_mem (hS0U hs))
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem_sup (hinf ⟨hcU, hc⟩) hs

theorem nonempty_quotient_centPair_equiv (hz : z ∈ L) (htL : ∀ l ∈ L, l * t = t * l)
    (hS0 : S0 ≤ centralizer (L : Set G)) (hS0c : ∀ a ∈ S0, ∀ b ∈ S0, a * b = b * a)
    (htS0 : t ∈ S0) (hC : centralizer ({t} : Set G) = L ⊔ S0) (hS02 : IsPGroup 2 S0) :
    Nonempty (↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t) ≃*
      ↥(L ⊓ centZ z) ⧸ CFSG.pCore 2 ↥(L ⊓ centZ z)) := by
  have hK := centPair_eq_sup hz htL hS0 hS0c htS0 hC
  obtain ⟨hO2, hN0U, hinf⟩ := O2In_centPair_eq hz htL hS0 hS0c htS0 hC hS02
  have hC0K : L ⊓ centZ z ≤ centPair z t := hK ▸ le_sup_left
  have hC0L : ((L ⊓ centZ z : Subgroup G) : Set G) ⊆ (L : Set G) := fun x hx => hx.1
  have hS0C0 : S0 ≤ centralizer ((L ⊓ centZ z : Subgroup G) : Set G) :=
    hS0.trans (Subgroup.centralizer_le hC0L)
  let φ : ↥(L ⊓ centZ z) →* ↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(centPair z t))).comp (Subgroup.inclusion hC0K)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    have hkK : (k : G) ∈ (L ⊓ centZ z) ⊔ S0 := by rw [← hK]; exact k.2
    obtain ⟨c, hc, s, hs, hks⟩ := exists_mul_of_mem_sup_of_le_centralizer hS0C0 hkK
    have hsK : s ∈ centPair z t := by rw [hK]; exact mem_sup_right hs
    have hsU : s ∈ O2In (centPair z t) := by rw [hO2]; exact mem_sup_right hs
    refine ⟨⟨c, hc⟩, ?_⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥(centPair z t)) (Subgroup.inclusion hC0K ⟨c, hc⟩) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(centPair z t)) k
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hmem : (⟨s, hsK⟩ : ↥(centPair z t)) ∈ CFSG.pCore 2 ↥(centPair z t) :=
      (mem_pCore_iff_mem_O2In _).2 hsU
    have : ((Subgroup.inclusion hC0K ⟨c, hc⟩)⁻¹ * k) = ⟨s, hsK⟩ := by
      apply Subtype.ext
      show c⁻¹ * (k : G) = s
      rw [hks, inv_mul_cancel_left]
    rw [this]
    exact hmem
  have hker : φ.ker = CFSG.pCore 2 ↥(L ⊓ centZ z) := by
    ext c
    rw [MonoidHom.mem_ker, mem_pCore_iff_mem_O2In]
    show QuotientGroup.mk' _ (Subgroup.inclusion hC0K c) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_pCore_iff_mem_O2In (H := centPair z t) (Subgroup.inclusion hC0K c)]
    exact ⟨fun h => hinf ⟨h, c.2⟩, fun h => hN0U h⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

noncomputable def centralizerEquivInf {L : Subgroup G} {z : G} (hz : z ∈ L) :
    centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L) ≃* ↥(L ⊓ centZ z) :=
  MulEquiv.ofBijective
    ({ toFun := fun y => ⟨(y : L), (y : L).2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩
       map_one' := rfl
       map_mul' := fun _ _ => rfl } :
      centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L) →* ↥(L ⊓ centZ z))
    ⟨fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      exact h', fun k => by
      refine ⟨⟨⟨k, k.2.1⟩, ?_⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 k.2.2)⟩

end KStructure

section Setting

variable [Finite G] {L : Subgroup G} {t z : G}


theorem Setting.exists_kStructure (h : Setting G L t) (hc : CentralPair G L t z) :
    ∃ S0 : Subgroup G, S0 ≤ centralizer (L : Set G) ∧ IsPGroup 2 S0 ∧ IsCyclic S0 ∧ t ∈ S0 ∧
      centralizer ({t} : Set G) = L ⊔ S0 ∧ centPair z t = (L ⊓ centZ z) ⊔ S0 ∧
      O2In (centPair z t) = O2In (L ⊓ centZ z) ⊔ S0 ∧
      Nonempty (↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t) ≃* Carrier .Co2) := by
  obtain ⟨S, hScyc, htS, hCt⟩ := h.exists_cyclic_sylow_centralizer_eq
  let S0 : Subgroup G :=
    (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
  let f : ↥S ≃* ↥S0 := Subgroup.equivMapOfInjective (S : Subgroup (centralizer (L : Set G)))
    (centralizer (L : Set G)).subtype (centralizer (L : Set G)).subtype_injective
  have hS0L : S0 ≤ centralizer (L : Set G) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hS02 : IsPGroup 2 S0 := (S.isPGroup').of_equiv f
  have hS0cyc : IsCyclic ↥S0 := isCyclic_of_surjective f.toMonoidHom f.surjective
  have hS0c : ∀ a ∈ S0, ∀ b ∈ S0, a * b = b * a := by
    intro a ha b hb
    have := (IsMulCommutative.is_comm : Std.Commutative (· * · : ↥S0 → ↥S0 → ↥S0)).comm
      ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have htS0 : t ∈ S0 := ⟨_, htS, rfl⟩
  have htL : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 h.mem_centralizer l hl
  obtain ⟨hO2, hN0U, hinf⟩ := O2In_centPair_eq hc.hz htL hS0L hS0c htS0 hCt hS02
  obtain ⟨e⟩ := nonempty_quotient_centPair_equiv hc.hz htL hS0L hS0c htS0 hCt hS02
  obtain ⟨f2⟩ := hc.loc.co2
  let α := centralizerEquivInf hc.hz
  have hα : (CFSG.pCore 2 ↥(centralizer ({(⟨z, hc.hz⟩ : ↥L)} : Set ↥L))).map α.toMonoidHom =
      CFSG.pCore 2 ↥(L ⊓ centZ z) := CFSG.pCore_map_iso 2 α
  let q := QuotientGroup.congr (CFSG.pCore 2 ↥(centralizer ({(⟨z, hc.hz⟩ : ↥L)} : Set ↥L)))
    (CFSG.pCore 2 ↥(L ⊓ centZ z)) α hα
  exact ⟨S0, hS0L, hS02, hS0cyc, htS0, hCt, centPair_eq_sup hc.hz htL hS0L hS0c htS0 hCt, hO2,
    ⟨e.trans (q.symm.trans f2)⟩⟩

end Setting


end CFSG.EvenSporadicStandard.TwoB

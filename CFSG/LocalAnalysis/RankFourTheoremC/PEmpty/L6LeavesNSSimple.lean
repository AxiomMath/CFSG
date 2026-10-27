module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSZ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSSection
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmThree

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace L6LeavesNS

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

theorem mem_plane_of_commute {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    {Q B : Subgroup A} (hQ : Open.pRank p Q ≤ 2) (hBQ : B ≤ Q) (hB : IsElemAbelian p B)
    (hBcard : Nat.card B = p ^ 2) {w : A} (hwQ : w ∈ Q) (hwp : w ^ p = 1)
    (hw : ∀ b ∈ B, b * w = w * b) : w ∈ B := by
  by_contra hwB
  have hcomm : ∀ a ∈ B, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a w from hw a ha) k).eq
  have hel := SU1.IsElemAbelian.sup hB (SU1.isElemAbelian_zpowers hwp) hcomm
  obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card hp hel
  have hlt : B < B ⊔ zpowers w := by
    refine lt_of_le_of_ne le_sup_left fun h => hwB ?_
    rw [h]
    exact mem_sup_right (mem_zpowers w)
  have hcard := SU1.card_lt_of_lt hlt
  rw [hBcard, hk] at hcard
  have hk3 : 3 ≤ k := by
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcard
    omega
  have hle : k ≤ Open.pRank p Q := SU1.le_pRank hp.one_lt (sup_le hBQ (zpowers_le.mpr hwQ)) hel hk
  omega

theorem pRank_comap_le_one {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (O : Subgroup Y) [O.Normal] (hO : Nat.Coprime p (Nat.card O)) {K : Subgroup (Y ⧸ O)}
    (hK : Open.pRank p K ≤ 1) : Open.pRank p (K.comap (QuotientGroup.mk' O)) ≤ 1 := by
  refine SU1.pRank_le_of fun E hE hEl k hk => ?_
  have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hEl
  have hle : E.map (QuotientGroup.mk' O) ≤ K := fun y ⟨e, he, hey⟩ => hey ▸ hE he
  have hcard : Nat.card (E.map (QuotientGroup.mk' O)) = p ^ k := by
    rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp O hO hEp, hk]
  exact (SU1.le_pRank hp.one_lt hle (CFSG.Open.IsElemAbelian.map hEl _) hcard).trans hK

end L6LeavesNS

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

theorem s622KFactSimple_holds : S622KFactSimple := by
  intro A _ _ p x z Q M hp hp5 _ hxo hzo hxz hxnz hQsyl hBQ hQz hQ2 hxfr hwc hQM hNz hΓ2 _ hnc
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set X : Subgroup A := centralizer ({x} : Set A) with hX
  have hxX : x ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzX : z ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm
  have hQX : Q ≤ X := hQsyl.le
  have hQp : IsPGroup p Q := hQsyl.isPGroup
  have hxp : x ^ p = 1 := by
    rw [← hxo]
    exact pow_orderOf_eq_one x
  have hzp : z ^ p = 1 := by
    rw [← hzo]
    exact pow_orderOf_eq_one z
  have hx1 : x ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  have hznx : z ∉ zpowers x := by
    intro hz
    apply hxnz
    have heq : zpowers z = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hzo])
    rw [heq]
    exact mem_zpowers x
  set B : Subgroup A := zpowers x ⊔ zpowers z with hB
  have hcommxz : ∀ a ∈ zpowers x, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute x z from hxz) i j).eq
  have hBc : Nat.card B = p ^ 2 := by
    rw [hB, CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers x) hzp hznx
      (fun e he => hcommxz e he z (mem_zpowers z)), Nat.card_zpowers, hxo, pow_two]
  have hBel : IsElemAbelian p B :=
    SU1.IsElemAbelian.sup (SU1.isElemAbelian_zpowers hxp) (SU1.isElemAbelian_zpowers hzp)
      hcommxz
  have hxB : x ∈ B := mem_sup_left (mem_zpowers x)
  have hzB : z ∈ B := mem_sup_right (mem_zpowers z)
  have hxQ : x ∈ Q := hBQ hxB
  have hzQ : z ∈ Q := hBQ hzB
  have hΩ : ∀ q ∈ Q, q ^ p = 1 → q ∈ B := by
    intro q hq hqp
    refine L6LeavesNS.mem_plane_of_commute hp hQ2 hBQ hBel hBc hq hqp fun b hb => ?_
    have hBc' : B ≤ centralizer ({q} : Set A) := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
          (hQX hq)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
          (hQz hq)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hBc' hb)
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a :=
    L6LeavesNS.sylow_centralizer_x_abelian hp2 hQp hxQ
      (fun q hq => Subgroup.mem_centralizer_singleton_iff.mp (hQX hq)) hxo hxfr hBQ hBc hxB hΩ
  set O : Subgroup ↥X := primeComplementCore (G := ↥X) p with hO
  have hOc : Nat.Coprime p (Nat.card O) := XBar.coprime p X
  set π : ↥X →* XBar p X := XBar.mk p X with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set x' : ↥X := ⟨x, hxX⟩ with hx'
  set z' : ↥X := ⟨z, hzX⟩ with hz'
  have hQ'p : IsPGroup p (Q.subgroupOf X) := hQp.comap_subtype
  have hQs : ¬ p ∣ (Q.subgroupOf X).index := ((CFSG.ABGLocalTools.isSylowOf_iff).1 hQsyl).2.2
  obtain ⟨Qb, hQb⟩ := XBar.exists_sylow hQ'p hQs
  have hinj : Set.InjOn π (Q.subgroupOf X) := injOn_mk_of_isPGroup hp O hOc hQ'p
  have hxQ' : x' ∈ Q.subgroupOf X := hxQ
  have hzQ' : z' ∈ Q.subgroupOf X := hzQ
  have hx'o : orderOf x' = p := by rw [Subgroup.orderOf_mk, hxo]
  have hz'o : orderOf z' = p := by rw [Subgroup.orderOf_mk, hzo]
  have hπx1 : π x' ≠ 1 := (XBar.element hp hQp hQX hBQ hxB hx1).2
  have hπz1 : π z' ≠ 1 := (XBar.element hp hQp hQX hBQ hzB hz1).2
  have hx'p : x' ^ p = 1 := by
    have := pow_orderOf_eq_one x'
    rwa [hx'o] at this
  have hz'p : z' ^ p = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'o] at this
  have hπxp : (π x') ^ p = 1 := by rw [← map_pow, hx'p, map_one]
  have hπzp : (π z') ^ p = 1 := by rw [← map_pow, hz'p, map_one]
  have hB'map : (zpowers x' ⊔ zpowers z').map X.subtype = B := by
    rw [hB, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hS : L6LeavesNS.AbSetup p Qb (π x') (π z') := by
    refine ⟨hp, hp2, primeComplementCore_quotient_eq_bot p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb
      rw [hQb] at ha hb
      obtain ⟨a₀, ha₀, rfl⟩ := ha
      obtain ⟨b₀, hb₀, rfl⟩ := hb
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (hQab a₀ ha₀ b₀ hb₀))
    · rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g₀, rfl⟩ := hπsurj g
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g₀.2))
    · exact orderOf_eq_prime hπxp hπx1
    · rw [hQb]
      exact ⟨x', hxQ', rfl⟩
    · rw [hQb]
      exact ⟨z', hzQ', rfl⟩
    · exact orderOf_eq_prime hπzp hπz1
    · intro hmem
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      rw [← map_zpow] at hk
      have hz'k : z' ^ k ∈ Q.subgroupOf X := Subgroup.zpow_mem _ hzQ' k
      have := hinj hz'k hxQ' hk
      apply hxnz
      exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val this⟩
    · intro q hq hqp
      rw [hQb] at hq
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      have hq₀p : q₀ ^ p = 1 :=
        hinj (Subgroup.pow_mem _ hq₀ p) (one_mem _) (by rw [map_pow, hqp, map_one])
      have hq₀A : (q₀ : A) ^ p = 1 := by simpa using congrArg Subtype.val hq₀p
      have hq₀B : (q₀ : A) ∈ B := hΩ _ hq₀ hq₀A
      have hq₀' : q₀ ∈ zpowers x' ⊔ zpowers z' := by
        rw [← hB'map] at hq₀B
        obtain ⟨w, hw, hwq⟩ := hq₀B
        exact (Subtype.ext hwq : w = q₀) ▸ hw
      have := Subgroup.mem_map_of_mem π hq₀'
      rwa [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
  set Y : Subgroup A := (M ⊓ X) ⊔ rankThreePrimeCore p X with hY
  have hMX : M ⊓ X ≤ Y := le_sup_left
  have hDY : rankThreePrimeCore p X ≤ Y := le_sup_right
  set Mb : Subgroup (XBar p X) := (Y.subgroupOf X).map π with hMb
  have hSM : (Qb : Subgroup (XBar p X)) ≤ Mb := by
    rw [hQb]
    exact Subgroup.map_mono fun q hq => hMX ⟨hQM hq, q.2⟩
  have hΓ2' : ∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y :=
    fun S hS hk g hg => hMX ⟨hΓ2 S hS hk hg.1, hg.2⟩
  have hΓ2Z : ∀ T : Subgroup (XBar p X), T ≤ (Qb : Subgroup (XBar p X)) → 2 ≤ Open.pRank p T →
      normalizer (T : Set (XBar p X)) ≤ Mb := by
    intro T hT hk
    exact XBar.gamma2 hp hQ'p hΓ2' (by rw [← hQb]; exact hT) hk
  have hπzpow : (zpowers z').map π = zpowers (π z') := MonoidHom.map_zpowers π z'
  have hNzZ : normalizer ((zpowers (π z') : Subgroup (XBar p X)) : Set (XBar p X)) ≤ Mb := by
    have hRp : IsPGroup p (zpowers z') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'o, pow_one])
    have hmapz : (zpowers z').map X.subtype = zpowers z := by
      rw [MonoidHom.map_zpowers]
      rfl
    refine normalizer_le_map_of_gamma hp O hOc hRp (Y' := Y.subgroupOf X) (k := 1) ?_
      (le_of_eq hπzpow.symm) (P64Free.one_le_pRank_zpowers hp hπzp hπz1)
    intro S hSR hk
    obtain ⟨E, hES, hEl, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank hp hk
    have hEeq : E = zpowers z' := Subgroup.eq_of_le_of_card_ge (hES.trans hSR)
      (by rw [hEc, Nat.card_zpowers, hz'o, pow_one])
    have hSeq : S = zpowers z' := le_antisymm hSR (hEeq ▸ hES)
    rw [hSeq]
    refine normalizer_subgroupOf_le (zpowers z') ?_
    rw [hmapz]
    exact fun g hg => hMX ⟨hNz hg.1, hg.2⟩
  have hB'p : IsPGroup p ↥(zpowers x' ⊔ zpowers z') :=
    hQ'p.to_le (sup_le (zpowers_le.mpr hxQ') (zpowers_le.mpr hzQ'))
  have hB'c : Nat.card ↥(zpowers x' ⊔ zpowers z') = p ^ 2 := by
    rw [← hBc, ← hB'map]
    exact (Subgroup.card_map_of_injective X.subtype_injective).symm
  have hNBZ : normalizer ((zpowers (π x') ⊔ zpowers (π z') : Subgroup (XBar p X)) :
      Set (XBar p X)) ≤ normalizer ((zpowers (π z') : Subgroup (XBar p X)) : Set (XBar p X)) := by
    have hmap : (zpowers x' ⊔ zpowers z').map π = zpowers (π x') ⊔ zpowers (π z') := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    have hk2 : 2 ≤ Open.pRank p (zpowers (π x') ⊔ zpowers (π z')) :=
      SU1.le_pRank hp.one_lt le_rfl hS.plane_elem hS.card_plane
    have h1 := normalizer_le_map_of_gamma hp O hOc hB'p
      (Y' := normalizer ((zpowers z' : Subgroup ↥X) : Set ↥X)) (k := 2) ?_
      (le_of_eq hmap.symm) hk2
    · intro g hg
      obtain ⟨n, hn, rfl⟩ := h1 hg
      have h2 : π n ∈ normalizer (((zpowers z').map π : Subgroup (XBar p X)) :
          Set (XBar p X)) := Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hn)
      rwa [hπzpow] at h2
    · intro S hSR hk
      obtain ⟨E, hES, hEl, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank hp hk
      have hEeq : E = zpowers x' ⊔ zpowers z' :=
        Subgroup.eq_of_le_of_card_ge (hES.trans hSR) (by rw [hEc, hB'c])
      have hSeq : S = zpowers x' ⊔ zpowers z' := le_antisymm hSR (hEeq ▸ hES)
      rw [hSeq]
      intro g hg
      refine L6LeavesNS.mem_normalizer_of_map_conj_le ?_
      rw [MonoidHom.map_zpowers]
      refine zpowers_le.mpr ?_
      have hgz : g * z' * g⁻¹ ∈ zpowers x' ⊔ zpowers z' :=
        (mem_normalizer_iff.mp hg z').mp (mem_sup_right (mem_zpowers z'))
      have hA : (g : A) * z * (g : A)⁻¹ ∈ B := by
        rw [← hB'map]
        exact ⟨_, hgz, rfl⟩
      obtain ⟨k, hk'⟩ := mem_zpowers_iff.mp (hwc (g : A) hA)
      exact mem_zpowers_iff.mpr ⟨k, Subtype.ext hk'⟩
  have hMtop : ¬ ⊤ ≤ Mb := XBar.not_top_le hDY hnc
  obtain ⟨K, hK, hKs, hKn, hzK, hKr, hKM, hMK⟩ :=
    hS.exists_component hSM hΓ2Z hNzZ hNBZ hMtop
  set K' : Subgroup ↥X := K.comap π with hK'
  have hz'K' : z' ∈ K' := hzK
  have hL : (K'.map X.subtype).subgroupOf X = K' :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective K'
  refine ⟨K'.map X.subtype, ?_, Subgroup.map_subtype_le K', ⟨z', hz'K', rfl⟩, ?_, ?_, ?_⟩
  · have hsec : S622IsSimpleSection K' π.ker :=
      L6LeavesNS.s622IsSimpleSection_comap π hπsurj hKs hKn
    have hsec' := L6LeavesNS.s622IsSimpleSection_map X.subtype X.subtype_injective hsec
    have hker : π.ker = O := QuotientGroup.ker_mk' O
    rw [hker] at hsec'
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.rankThreePrimeCore_eq_map_primeComplementCore]
    exact hsec'
  · rw [pRank_map_subtype hp.one_lt]
    exact L6LeavesNS.pRank_comap_le_one hp O hOc hKr
  · intro hle
    apply hKM
    intro k hk
    obtain ⟨l, rfl⟩ := hπsurj k
    have hlK' : l ∈ K' := hk
    have hlL : (l : A) ∈ K'.map X.subtype := ⟨l, hlK', rfl⟩
    have hle2 : (M ⊓ K'.map X.subtype) ⊔ rankThreePrimeCore p X ≤ Y :=
      sup_le_sup_right (inf_le_inf_left M (Subgroup.map_subtype_le K')) _
    have hlY : (l : A) ∈ Y := hle2 (hle hlL)
    exact ⟨l, hlY, rfl⟩
  · intro m hm
    have hm' : (⟨m, hm.2⟩ : ↥X) ∈ Y.subgroupOf X := hMX hm
    have h1 : π ⟨m, hm.2⟩ ∈ Mb := ⟨_, hm', rfl⟩
    have h2 := L6LeavesNS.mem_normalizer_comap π (hMK h1)
    have h3 : (⟨m, hm.2⟩ : ↥X) ∈
        normalizer (((K'.map X.subtype).subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      rw [hL]
      exact h2
    exact P64Free.mem_normalizer_of_mem_normalizer_subgroupOf (Subgroup.map_subtype_le K') h3

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

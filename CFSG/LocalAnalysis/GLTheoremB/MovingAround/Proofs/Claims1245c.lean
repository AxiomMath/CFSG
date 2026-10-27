module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1245b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123b
public import CFSG.HardMathSupport.Solomon.Coordinator.I2_5

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1245c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf autBar innerAut)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open scoped commutatorElement

@[expose] def Input14_17 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → y ^ 3 = 1 →
    ∀ J : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) J →
      IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
      IsChevSimple 2 (barOf 3 L ⧸ Subgroup.center (barOf 3 L))

section Generic

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_of_modCenter {J : Subgroup G}
    (h : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) : 3 ∣ Nat.card J := by
  have h1 := CFSG.HardMathSupport.Solomon.Coordinator.card_of_isLThreeFour h
  have h2 : 3 ∣ Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) := by rw [h1]; norm_num
  exact (h2.trans (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_quotient_dvd_card _)

theorem isLThreeFour_quot_center' {X D : Type} [Group X] [Group D]
    (hX : CFSG.Open.IsQuasisimple X) (Z : Subgroup X) [Z.Normal] (φ : D ≃* X ⧸ Z)
    (h : IsLThreeFour (D ⧸ Subgroup.center D)) : IsLThreeFour (X ⧸ Subgroup.center X) := by
  obtain ⟨hsimple, a, b, hab⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour h
  let ψ : X →* D ⧸ Subgroup.center D :=
    (QuotientGroup.mk' (Subgroup.center D)).comp (φ.symm.toMonoidHom.comp (QuotientGroup.mk' Z))
  have hsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (φ.symm.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker = Subgroup.center X := by
    apply le_antisymm
    · refine CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hX ψ.ker ?_
      intro htop
      have hnt : Nontrivial (D ⧸ Subgroup.center D) := ⟨a, b, fun hh => hab (by rw [hh])⟩
      obtain ⟨u, hu⟩ := exists_ne (1 : D ⧸ Subgroup.center D)
      obtain ⟨x, rfl⟩ := hsurj u
      exact hu (MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top x))
    · intro x hx
      have hc : ψ x ∈ Subgroup.center (D ⧸ Subgroup.center D) := by
        refine Subgroup.mem_center_iff.2 fun g => ?_
        obtain ⟨y, rfl⟩ := hsurj g
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx y)]
      rw [CFSG.ComponentClassification.Helpers.center_eq_bot _ ⟨a, b, hab⟩] at hc
      exact Subgroup.mem_bot.1 hc
  have e : X ⧸ Subgroup.center X ≃* D ⧸ Subgroup.center D :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)
  exact Lemma1245.isLThreeFour_congr e.symm h

theorem barAut_eq_one_of_comm {J : Subgroup G} {u : G} (hu : u ∈ Subgroup.normalizer (J : Set G))
    (h : ∀ l ∈ J, u * l * u⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf 3 J) : barAut 3 J ⟨u, hu⟩ = 1 :=
  (Lemma129.mem_centBar_top_iff hu).1
    ((Claims1245b.mem_centBar_forall_iff).2 ⟨Subgroup.mem_top _, hu, h⟩)

theorem inf_glaPPrimeCoreOf_le {J X : Subgroup G} (hJX : J ≤ X) :
    J ⊓ GLAPPrimeCoreOf 3 X ≤ GLAPPrimeCoreOf 3 J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine sec11_le_glaPPrimeCoreOf inf_le_left (fun h hh n hn =>
    ⟨J.mul_mem (J.mul_mem hh hn.1) (J.inv_mem hh),
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 X (hJX hh)) n).1 hn.2⟩) ?_
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
    (fun hd => not_dvd_card_glaPPrimeCoreOf Nat.prime_three X
      (hd.trans (Subgroup.card_dvd_of_le inf_le_right)))

theorem exists_not_mem_zpowers {F : Subgroup G} (hFel : IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    {x : G} (hxF : x ∈ F) : ∃ y ∈ F, y ∉ Subgroup.zpowers x := by
  by_contra hcon
  push Not at hcon
  have hle : Nat.card F ≤ Nat.card (Subgroup.zpowers x) :=
    Subgroup.card_le_of_le (fun y hy => hcon y hy)
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hFel.2 x hxF)
  have hle3 : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  rw [Nat.card_zpowers, hF9] at hle
  omega

theorem orderOf_eq_three_of_mem_zpowers {y d : G} (hy : y ^ 3 = 1) (hd : d ∈ Subgroup.zpowers y)
    (hd1 : d ≠ 1) : orderOf d = 3 := by
  have hd3 : d ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  exact orderOf_eq_prime hd3 hd1

theorem eq_zpowers_sup {F : Subgroup G} (hFel : IsElemAbelian 3 F) (hF9 : Nat.card F = 9) {x y : G}
    (hxF : x ∈ F) (hx1 : x ≠ 1) (hyF : y ∈ F) (hyx : y ∉ Subgroup.zpowers x) :
    F = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
  have hx3 : x ^ 3 = 1 := hFel.2 x hxF
  have hy3 : y ^ 3 = 1 := hFel.2 y hyF
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hcomm : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers y, u * v = v * u := fun u hu v hv =>
    CFSG.Open.IsElemAbelian.comm hFel (Subgroup.zpowers_le.2 hxF hu) (Subgroup.zpowers_le.2 hyF hv)
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    by_contra hne
    obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzo : orderOf z = 3 := orderOf_eq_three_of_mem_zpowers hy3 hz.2 hz1'
    have h1 : Subgroup.zpowers z = Subgroup.zpowers y := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz.2) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hzo]
    apply hyx
    have : y ∈ Subgroup.zpowers z := h1 ▸ Subgroup.mem_zpowers y
    exact Subgroup.zpowers_le.2 hz.1 this
  have hcard : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = 9 := by
    rw [Lemma124.card_eq_mul_of_sup_eq hcomm rfl hdisj, Nat.card_zpowers, Nat.card_zpowers, hxo, hyo]
  exact (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.2 hxF) (Subgroup.zpowers_le.2 hyF))
    (by rw [hcard, hF9])).symm

theorem inf_centralizer_eq {F : Subgroup G} {x y : G} (hF : F = Subgroup.zpowers x ⊔ Subgroup.zpowers y)
    (hyF : y ∈ F) :
    Cg x ⊓ Subgroup.centralizer (F : Set G) = Cg x ⊓ Subgroup.centralizer ({y} : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (Sec12b.cent_le_cent_of_mem hyF)
  · rintro g ⟨hgx, hgy⟩
    refine ⟨hgx, ?_⟩
    have hle : F ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [hF]
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hgy).symm
    exact Subgroup.mem_centralizer_iff.2 fun f hf => Subgroup.mem_centralizer_singleton_iff.1 (hle hf)

theorem barX_eq_top_of_modCenter {Lx J : Subgroup G} (hJL : J ≤ Lx)
    (hq : CFSG.Open.IsQuasisimple (barOf 3 Lx))
    (hLt : IsLThreeFour (barOf 3 Lx ⧸ Subgroup.center (barOf 3 Lx)))
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) :
    barX 3 Lx J = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : ↥Lx →* barOf 3 Lx := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Lx) with hπ
  set ρ : barOf 3 Lx →* barOf 3 Lx ⧸ Subgroup.center (barOf 3 Lx) :=
    QuotientGroup.mk' (Subgroup.center (barOf 3 Lx)) with hρ
  set φ : ↥J →* barOf 3 Lx ⧸ Subgroup.center (barOf 3 Lx) := ρ.comp (π.comp (Subgroup.inclusion hJL))
    with hφ
  set ψ : ↥J →* barOf 3 J ⧸ Subgroup.center (barOf 3 J) :=
    (QuotientGroup.mk' (Subgroup.center (barOf 3 J))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
    with hψ
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ ψ.ker := by
    intro j hj
    have hc : π (Subgroup.inclusion hJL j) ∈ Subgroup.center (barOf 3 Lx) :=
      (QuotientGroup.eq_one_iff _).1 hj
    have hcent : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) j ∈ Subgroup.center (barOf 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨j', rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) w
      have h1 := Subgroup.mem_center_iff.1 hc (π (Subgroup.inclusion hJL j'))
      have h2 : π (Subgroup.inclusion hJL (j' * j)) = π (Subgroup.inclusion hJL (j * j')) := by
        simp only [map_mul]
        exact h1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
      have h3 : ((j' * j)⁻¹ * (j * j') : G) ∈ J ⊓ GLAPPrimeCoreOf 3 Lx :=
        ⟨J.mul_mem (J.inv_mem (J.mul_mem j'.2 j.2)) (J.mul_mem j.2 j'.2), ⟨_, h2, by simp⟩⟩
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (inf_glaPPrimeCoreOf_le hJL h3)
      have htv : t = (j' * j)⁻¹ * (j * j') := Subtype.ext (by simpa using hte)
      rw [htv] at ht
      have h5 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) (j' * j) =
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) (j * j') := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        exact ht
      simpa only [map_mul] using h5
    show QuotientGroup.mk' (Subgroup.center (barOf 3 J)) (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) j) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hcent
  have h1 : Nat.card ↥J = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have h2 : Nat.card ↥J = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hψr : Nat.card ψ.range = 20160 := by
    rw [MonoidHom.range_eq_top.2 hψs, Subgroup.card_top]
    exact CFSG.HardMathSupport.Solomon.Coordinator.card_of_isLThreeFour hJt
  have hk : Nat.card φ.ker ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hker
  have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hQ : Nat.card (barOf 3 Lx ⧸ Subgroup.center (barOf 3 Lx)) = 20160 :=
    CFSG.HardMathSupport.Solomon.Coordinator.card_of_isLThreeFour hLt
  have hφr : 20160 ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have h3 : Nat.card φ.range * Nat.card φ.ker < 20160 * Nat.card ψ.ker :=
      calc Nat.card φ.range * Nat.card φ.ker < 20160 * Nat.card φ.ker :=
            (Nat.mul_lt_mul_right hkpos).2 hlt
        _ ≤ 20160 * Nat.card ψ.ker := Nat.mul_le_mul_left _ hk
    rw [← h1, ← hψr, ← h2] at h3
    exact lt_irrefl _ h3
  have hφtop : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have := Subgroup.card_le_card_group φ.range
    omega
  have hdec : ∀ q : barOf 3 Lx, ∃ s ∈ barX 3 Lx J, ∃ z ∈ Subgroup.center (barOf 3 Lx), q = s * z := by
    intro q
    have hq' : ρ q ∈ φ.range := hφtop ▸ Subgroup.mem_top _
    obtain ⟨j, hj⟩ := hq'
    refine ⟨π (Subgroup.inclusion hJL j), ⟨Subgroup.inclusion hJL j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩,
      (π (Subgroup.inclusion hJL j))⁻¹ * q, ?_, by group⟩
    have h4 : ((π (Subgroup.inclusion hJL j) : barOf 3 Lx) : barOf 3 Lx ⧸ Subgroup.center (barOf 3 Lx)) =
        (q : barOf 3 Lx ⧸ Subgroup.center (barOf 3 Lx)) := hj
    exact QuotientGroup.eq.1 h4
  rw [eq_top_iff, ← hq.1, _root_.commutator_def]
  refine Subgroup.commutator_le.2 fun q₁ _ q₂ _ => ?_
  obtain ⟨s₁, hs₁, z₁, hz₁, rfl⟩ := hdec q₁
  obtain ⟨s₂, hs₂, z₂, hz₂, rfl⟩ := hdec q₂
  rw [show s₁ * z₁ = z₁ * s₁ from Subgroup.mem_center_iff.1 hz₁ s₁,
    show s₂ * z₂ = z₂ * s₂ from Subgroup.mem_center_iff.1 hz₂ s₂,
    Claims1245b.commutatorElement_mul_central (fun y => (Subgroup.mem_center_iff.1 hz₁ y).symm)
      (fun y => (Subgroup.mem_center_iff.1 hz₂ y).symm), commutatorElement_def]
  exact (barX 3 Lx J).mul_mem ((barX 3 Lx J).mul_mem ((barX 3 Lx J).mul_mem hs₁ hs₂)
    ((barX 3 Lx J).inv_mem hs₁)) ((barX 3 Lx J).inv_mem hs₂)

theorem covers_of_le {a : G} {K J M : Subgroup G} (hK : GLAPComponent 3 (Cg a) K) (hJK : J ≤ K)
    (hcov : barX 3 K J = ⊤) (hJM : J ≤ M) : Covers 3 (Cg a) (M ⊓ Cg a) K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro _ ⟨⟨k, hkC⟩, hk, rfl⟩
  have hk' : k ∈ K := Subgroup.mem_subgroupOf.1 hk
  obtain ⟨j, hj, o, ho, rfl⟩ := Sec12b.mem_mul_glaPPrimeCoreOf_of_barX hJK hcov hk'
  have hoC : o ∈ GLAPPrimeCoreOf 3 (Cg a) :=
    glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hK.2.1 ho
  have hjC : j ∈ Cg a := hK.1 (hJK hj)
  have hoC' : o ∈ Cg a := (Subgroup.map_subtype_le _ : GLAPPrimeCoreOf 3 (Cg a) ≤ Cg a) hoC
  refine ⟨⟨j, hjC⟩, Subgroup.mem_subgroupOf.2 ⟨hJM hj, hjC⟩, ?_⟩
  have e : (⟨j * o, hkC⟩ : ↥(Cg a)) = ⟨j, hjC⟩ * ⟨o, hoC'⟩ := Subtype.ext rfl
  rw [e, map_mul, (mem_glaPPrimeCoreOf_iff hoC').1 hoC, mul_one]

theorem exists_not_centralized {x u : G} {J Δ : Subgroup G} {𝒞 : Set (Subgroup G)}
    (h𝒞 : ∀ L ∈ 𝒞, L ≤ Cg x) (hJ : J ≤ ⨆ L ∈ 𝒞, L) (hJx : J ≤ Cg x)
    (huΔ : u ∈ Δ) (huX : u ∈ Cg x) (huN : u ∈ Subgroup.normalizer (J : Set G))
    (hu1 : barAut 3 J ⟨u, huN⟩ ≠ 1) :
    ∃ L ∈ 𝒞, ¬ barX 3 (Cg x) Δ ≤
      Subgroup.centralizer (barX 3 (Cg x) L : Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  apply hu1
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg x)) with hπ
  have hub : π ⟨u, huX⟩ ∈ barX 3 (Cg x) Δ := ⟨⟨u, huX⟩, Subgroup.mem_subgroupOf.2 huΔ, rfl⟩
  set H : Subgroup G := ((Subgroup.centralizer ({π ⟨u, huX⟩} :
    Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)))).comap π).map (Cg x).subtype with hH
  have hLH : ∀ L ∈ 𝒞, L ≤ H := by
    intro L hL l hl
    refine ⟨⟨l, h𝒞 L hL hl⟩, ?_, rfl⟩
    change π ⟨l, h𝒞 L hL hl⟩ ∈ Subgroup.centralizer ({π ⟨u, huX⟩} :
      Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlb : π ⟨l, h𝒞 L hL hl⟩ ∈ barX 3 (Cg x) L :=
      ⟨⟨l, h𝒞 L hL hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (hcon L hL hub) _ hlb
  have hJH : J ≤ H := hJ.trans (iSup₂_le hLH)
  refine barAut_eq_one_of_comm huN fun l hl => ?_
  have hlX : l ∈ Cg x := hJx hl
  have hcomm : π ⟨l, hlX⟩ * π ⟨u, huX⟩ = π ⟨u, huX⟩ * π ⟨l, hlX⟩ := by
    obtain ⟨⟨l', hl'X⟩, hl'c, hl'e⟩ := hJH hl
    have hl'' : l' = l := hl'e
    subst hl''
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 hl'c)
  have hmemX : u * l * u⁻¹ * l⁻¹ ∈ Cg x :=
    (Cg x).mul_mem ((Cg x).mul_mem ((Cg x).mul_mem huX hlX) ((Cg x).inv_mem huX)) ((Cg x).inv_mem hlX)
  have hcore : u * l * u⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf 3 (Cg x) := by
    rw [mem_glaPPrimeCoreOf_iff hmemX]
    change π ⟨u * l * u⁻¹ * l⁻¹, hmemX⟩ = 1
    have e : (⟨u * l * u⁻¹ * l⁻¹, hmemX⟩ : ↥(Cg x)) =
        ⟨u, huX⟩ * ⟨l, hlX⟩ * (⟨u, huX⟩ : ↥(Cg x))⁻¹ * (⟨l, hlX⟩ : ↥(Cg x))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have hJmem : u * l * u⁻¹ * l⁻¹ ∈ J :=
    J.mul_mem ((Subgroup.mem_normalizer_iff.1 huN l).1 hl) (J.inv_mem hl)
  exact inf_glaPPrimeCoreOf_le hJx ⟨hJmem, hcore⟩

theorem gLBConj_injective (g : G) {H₁ H₂ : Subgroup G} (h : GLBConj g H₁ = GLBConj g H₂) : H₁ = H₂ := by
  have := congrArg (GLBConj g⁻¹) h
  rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at this

theorem gLBConj_eq_of_mem_zpowers {x v : G} {L : Subgroup G} (hL : L ≤ Cg x)
    (hv : v ∈ Subgroup.zpowers x) : GLBConj v L = L := by
  refine gLBConj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  have h1 : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.1 (hL hl)
  exact (Commute.zpow_right h1 k).eq

theorem isLThreeFour_of_cycled {x y : G} {L₁ L₂ L₃ J : Subgroup G}
    (h₁ : GLAPComponent 3 (Cg x) L₁) (h₂ : GLAPComponent 3 (Cg x) L₂) (h₃ : GLAPComponent 3 (Cg x) L₃)
    (h12 : L₁ ≠ L₂) (h23 : L₂ ≠ L₃) (h31 : L₃ ≠ L₁)
    (hy₁ : GLBConj y L₁ = L₂) (hy₂ : GLBConj y L₂ = L₃) (hy₃ : GLBConj y L₃ = L₁)
    (hyX : y ∈ Cg x) (hy3 : y ^ 3 = 1)
    (hJ : GLAPComponent 3 (Cg x ⊓ Subgroup.centralizer ({y} : Set G)) J) (hJ123 : J ≤ L₁ ⊔ L₂ ⊔ L₃)
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) :
    IsLThreeFour (barOf 3 L₁ ⧸ Subgroup.center (barOf 3 L₁)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg x)) with hπ
  set X₁ := barX 3 (Cg x) L₁ with hX₁def
  set X₂ := barX 3 (Cg x) L₂ with hX₂def
  set X₃ := barX 3 (Cg x) L₃ with hX₃def
  have hX₁ : IsComponentOf X₁ ⊤ := h₁.2.2.1
  have hX₂ : IsComponentOf X₂ ⊤ := h₂.2.2.1
  have hX₃ : IsComponentOf X₃ ⊤ := h₃.2.2.1
  have hX12 : X₁ ≠ X₂ := fun h => h12 (glaPComponent_unique h₁ h₂ h)
  have hX23 : X₂ ≠ X₃ := fun h => h23 (glaPComponent_unique h₂ h₃ h)
  have hX31 : X₃ ≠ X₁ := fun h => h31 (glaPComponent_unique h₃ h₁ h)
  set yb := π ⟨y, hyX⟩ with hyb
  have hc₁ : GLBConj yb X₁ = X₂ := by rw [← barX_gLBConj_eq 3 hyX L₁, hy₁]
  have hc₂ : GLBConj yb X₂ = X₃ := by rw [← barX_gLBConj_eq 3 hyX L₂, hy₂]
  have hc₃ : GLBConj yb X₃ = X₁ := by rw [← barX_gLBConj_eq 3 hyX L₃, hy₃]
  have hyb3 : yb ^ 3 = 1 := by
    have h1 : (⟨y, hyX⟩ : ↥(Cg x)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [hyb, ← map_pow, h1, map_one]
  have hsup : barX 3 (Cg x) (L₁ ⊔ L₂ ⊔ L₃) = X₁ ⊔ X₂ ⊔ X₃ := by
    rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.barX_sup (sup_le h₁.1 h₂.1) h₃.1,
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.barX_sup h₁.1 h₂.1]
  set Ib := X₁ ⊔ X₂ ⊔ X₃ with hIbdef
  obtain ⟨hlay, -⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.components_of_product hX₁ hX₂ hX₃ hX12 hX23 hX31
  obtain ⟨hreg1, hreg2, hnormE, hel⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.regular_of_cycle hX₁ hX₂ hX₃ hX12 hX23 hX31
      hc₁ hc₂ hc₃ hyb3
  obtain ⟨h25a, h25b⟩ := CFSG.HardMathSupport.Solomon.Coordinator.input2_5_proved
    (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)) 3 hp3 Ib (Subgroup.zpowers yb) hlay hnormE hel hreg1 hreg2
  set C := Ib ⊓ Subgroup.centralizer ((Subgroup.zpowers yb : Subgroup _) :
    Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x))) with hCdef
  set D := GLALayer C with hDdef
  have hX₁Ib : IsComponentOf X₁ Ib :=
    ⟨le_sup_left.trans le_sup_left, isSubnormal_of_le_of_le hX₁.2.1
      (le_sup_left.trans le_sup_left) le_top, hX₁.2.2⟩
  obtain ⟨Z, hZn, hZc, ⟨φ⟩⟩ := h25a X₁ hX₁Ib
  have hqX₁ : CFSG.Open.IsQuasisimple ↥X₁ := hX₁.2.2
  have hDq : CFSG.Open.IsQuasisimple ↥D :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv φ
      (CFSG.ComponentClassification.Quasisimple.central_quotient hqX₁ Z hZc)
  have hZ₀ : ∀ z ∈ (Subgroup.center ↥Ib).map Ib.subtype ⊓
      Subgroup.centralizer ((Subgroup.zpowers yb : Subgroup _) :
        Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x))), ∀ c' ∈ C, z * c' = c' * z := by
    rintro z ⟨⟨z', hz', rfl⟩, -⟩ c' hc'
    have := Subgroup.mem_center_iff.1 hz' ⟨c', hc'.1⟩
    exact congrArg Subtype.val this.symm
  have hDC : D ≤ C := sSup_le fun K hK => hK.1
  set Jt := barX 3 (Cg x) J with hJtdef
  have hJX : J ≤ Cg x := hJ.1.trans inf_le_left
  have hJy : J ≤ Subgroup.centralizer ({y} : Set G) := hJ.1.trans inf_le_right
  have hJtcent : Jt ≤ Subgroup.centralizer ((Subgroup.zpowers yb : Subgroup _) :
      Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x))) := by
    rintro _ ⟨⟨j, hjX⟩, hj, rfl⟩
    rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.centralizer_zpowers_eq_singleton,
      Subgroup.mem_centralizer_singleton_iff, hyb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hJy (Subgroup.mem_subgroupOf.1 hj)))
  have hJtC : Jt ≤ C := le_inf (hsup ▸ barX_mono hJ123) hJtcent
  have hJtperf : ⁅Jt, Jt⁆ = Jt := barX_perfect 3 hJX (glaPComponent_perfect hJ)
  have hJtne : Jt ≠ ⊥ := Prop126b.barX_ne_bot_of_three_dvd hJX (three_dvd_card_of_modCenter hJt)
  have hJtD : Jt ≤ D := by
    have hCD := CFSG.HardMathSupport.Solomon.UniquenessMaximal.commutator_le_of_sup_central hDC h25b hZ₀
    calc Jt = ⁅Jt, Jt⁆ := hJtperf.symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hJtC hJtC
      _ ≤ D := hCD
  have hJcomp' := Prop126b.glaPComponent_barX_inf_centralizer hp3 hyX le_rfl (Subgroup.le_normalizer hyX)
    (l119_isPGroup_zpowers hy3) hJ
  rw [barX_self, top_inf_eq] at hJcomp'
  have hDle : D ≤ Subgroup.centralizer ({yb} : Set (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x))) :=
    hDC.trans (inf_le_right.trans
      (le_of_eq (CFSG.HardMathSupport.Solomon.UniquenessMaximal.centralizer_zpowers_eq_singleton yb)))
  have hJtsn : IsSubnormal Jt D := isSubnormal_of_le_of_le hJcomp'.2.1 hJtD hDle
  have hJtD' : Jt = D := Prop126b.eq_of_subnormal_perfect hDq hJtsn hJtperf hJtne
  have hJtq : CFSG.Open.IsQuasisimple ↥Jt :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv (MulEquiv.subgroupCongr hJtD') hDq
  have hJt1 : IsLThreeFour ((↥Jt ⧸ GLAPPrimeCore 3 ↥Jt) ⧸ Subgroup.center (↥Jt ⧸ GLAPPrimeCore 3 ↥Jt)) :=
    Lemma1245.isLThreeFour_modCenter_congr (Prop126b.barOfBarX hp3 hJX) hJt
  have hJt2 : IsLThreeFour (↥Jt ⧸ Subgroup.center ↥Jt) :=
    isLThreeFour_quot_center' hJtq (GLAPPrimeCore 3 ↥Jt) (MulEquiv.refl _) hJt1
  have hD2 : IsLThreeFour (↥D ⧸ Subgroup.center ↥D) :=
    Lemma1245.isLThreeFour_modCenter_congr (MulEquiv.subgroupCongr hJtD') hJt2
  have hX₁t : IsLThreeFour (↥X₁ ⧸ Subgroup.center ↥X₁) := isLThreeFour_quot_center' hqX₁ Z φ hD2
  exact Lemma1245.isLThreeFour_modCenter_congr (quotEquivBarX hp3 h₁.1 h₁.2.1).symm hX₁t

end Generic

section Unitary

variable {G : Type} [Group G] [Finite G]

theorem exists_unitary_cent_A' {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex121 G m 3 B M E A a) (hdec : A = (E ⊓ A) ⊔ Lemma1245.FF A K)
    (hT₀N : Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hu : ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩)) :
    ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  obtain ⟨u₀, hu₀, hu₀N, hu₀U⟩ := hu
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hFA : Lemma1245.FF A K ≤ A := inf_le_right
  have hA0A : E ⊓ A ≤ A := inf_le_right
  have hAα : A ≤ Subgroup.normalizer ((alphaOf 3 M ⊓ Cg a : Subgroup G) : Set G) := by
    intro k hk
    have hkM : k ∈ M := hAM hk
    have hkCa : k ∈ Cg a := by
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      exact CFSG.Open.IsElemAbelian.comm hAel h.ha.1 hk
    exact Sec12a.mem_normalizer_inf (le_normalizer_alphaOf 3 M hkM) (Subgroup.le_normalizer hkCa)
  have hAT : A ≤ Subgroup.normalizer ((Tof 3 M a : Subgroup G) : Set G) :=
    hAα.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (alphaOf 3 M ⊓ Cg a))
  set T₀ : Subgroup G := Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) with hT₀
  have hFT₀ : Lemma1245.FF A K ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro f hf
    exact Prop121.normalizer_inf_mem (hAT (hFA hf))
      (Lemma1245.mem_normalizer_centralizer_of_comm fun b hb =>
        CFSG.Open.IsElemAbelian.comm hAel (hA0A hb) (hFA hf))
  have hT₀2 : IsPGroup 2 ↥T₀ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (alphaOf 3 M ⊓ Cg a)).to_le inf_le_left
  have hT₀cop : ¬ 3 ∣ Nat.card ↥T₀ := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT₀2
    rw [hn]
    intro hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp3 Nat.prime_two).1 (hp3.dvd_of_dvd_pow hd))
      (by norm_num)
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 hp3 (Lemma1245.FF A K) T₀
    (Lemma124.isPGroup_three_of_isElemAbelian (Lemma124.isElemAbelian_of_le hFA hAel)) hT₀cop hFT₀
  have hu₀T : u₀ ∈ T₀ := hu₀
  have hPJ : T₀ ⊓ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((⁅T₀, Lemma1245.FF A K⁆ : Subgroup G) : Set G) :=
    inf_le_left.trans (Subgroup.normalizer_commutator_ge_left T₀ (Lemma1245.FF A K))
  obtain ⟨c, hc, r, hr, hcr⟩ := Prop121.mem_sup_decomp hPJ
    (show u₀ ∈ (T₀ ⊓ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G)) ⊔
        ⁅T₀, Lemma1245.FF A K⁆ by
      rw [sup_comm, ← hfac]
      exact hu₀T)
  have hrK : ⁅T₀, Lemma1245.FF A K⁆ ≤ centBar 3 ⊤ K := by
    refine Subgroup.commutator_le.2 fun t ht f hf => ?_
    obtain ⟨hfN, hfbar⟩ := Lemma1245.centBar_barAut_eq_one hf
    have htN : t ∈ Subgroup.normalizer (K : Set G) := hT₀N ht
    have hγ : barAut 3 K
        ⁅(⟨t, htN⟩ : ↥(Subgroup.normalizer (K : Set G))), ⟨f, hfN⟩⁆ = 1 := by
      rw [map_commutatorElement, hfbar, commutatorElement_one_right]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨_, MonoidHom.mem_ker.2 hγ, rfl⟩,
      Subgroup.mem_top _⟩
  obtain ⟨hrN, hrbar⟩ := Lemma1245.centBar_barAut_eq_one (hrK hr)
  have hceq : c = u₀ * r⁻¹ := by rw [hcr]; group
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := by
    rw [hceq]
    exact Subgroup.mul_mem _ hu₀N (Subgroup.inv_mem _ hrN)
  have hcomm : ∀ b ∈ E ⊓ A, ∀ f ∈ Lemma1245.FF A K, b * f = f * b := fun b hb f hf =>
    CFSG.Open.IsElemAbelian.comm hAel (hA0A hb) (hFA hf)
  refine ⟨c, ⟨hc.1.1, ?_⟩, hcN, ?_⟩
  · show c ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxsup : x ∈ (E ⊓ A) ⊔ Lemma1245.FF A K := hdec ▸ hx
    obtain ⟨b, hb, f, hf, rfl⟩ := Lemma124.exists_mul_of_mem_sup hcomm hxsup
    have h1 : b * c = c * b := Subgroup.mem_centralizer_iff.1 hc.1.2 b hb
    have h2 : f * c = c * f := Subgroup.mem_centralizer_iff.1 hc.2 f hf
    calc b * f * c = b * (f * c) := by group
      _ = b * (c * f) := by rw [h2]
      _ = (b * c) * f := by group
      _ = (c * b) * f := by rw [h1]
      _ = c * (b * f) := by group
  · have hbar : barAut 3 K ⟨c, hcN⟩ = barAut 3 K ⟨u₀, hu₀N⟩ := by
      have : (⟨u₀, hu₀N⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨c, hcN⟩ * ⟨r, hrN⟩ :=
        Subtype.ext hcr
      rw [this, map_mul, hrbar, mul_one]
    rw [hbar]
    exact hu₀U

end Unitary

structure KxCtx (G : Type) [Group G] [Finite G] (m : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G) :
    Prop where
  h : Cex121 G m 3 B M E A a
  hK : GLAPComponent 3 (Cg a) K
  hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K))
  hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K
  hu₀ : ∃ u ∈ Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
    ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩)
  hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K
  hAN : A ≤ Subgroup.normalizer (K : Set G)

namespace KxCtx

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
  (c : KxCtx G m B M E A a K)
include c

theorem elemAbelian : IsElemAbelian 3 A := c.h.pair.1.2.1.1.1.2.1

theorem le_M : A ≤ M := c.h.pair.1.2.1.1.1.1

theorem comm {b b' : G} (hb : b ∈ A) (hb' : b' ∈ A) : b * b' = b' * b :=
  CFSG.Open.IsElemAbelian.comm c.elemAbelian hb hb'

theorem le_cg {x : G} (hx : x ∈ A) : A ≤ Cg x := fun b hb =>
  Subgroup.mem_centralizer_singleton_iff.2 (c.comm hb hx)

theorem ff_le : Lemma1245.FF A K ≤ A := inf_le_right

theorem ff_elem : IsElemAbelian 3 (Lemma1245.FF A K) :=
  Lemma124.isElemAbelian_of_le c.ff_le c.elemAbelian

theorem a_mem_ff : a ∈ Lemma1245.FF A K := Lemma1245.mem_centBar_of_component c.h.ha.1 c.hK.1

theorem quasisimple : CFSG.Open.IsQuasisimple (barOf 3 K) :=
  l119_isQuasisimple_barOf (p := 3) Nat.prime_three c.hK

theorem jj_le_K : Lemma1245.JJ A K ≤ K := (Sec12b.layer_le 3 _).trans inf_le_left

theorem jj_cent : Lemma1245.JJ A K ≤ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G) :=
  (Sec12b.layer_le 3 _).trans inf_le_right

theorem cover : barX 3 K (Lemma1245.JJ A K) = ⊤ := Lemma1245.barX_JJ_eq_top c.elemAbelian c.quasisimple

theorem jj_quasisimple : CFSG.Open.IsQuasisimple (barOf 3 (Lemma1245.JJ A K)) := by
  obtain ⟨e, -⟩ := Lemma1245.exists_barOf_equiv_of_cover (p := 3) Nat.prime_three c.jj_le_K c.cover
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm c.quasisimple

theorem jj_type :
    IsLThreeFour (barOf 3 (Lemma1245.JJ A K) ⧸ Subgroup.center (barOf 3 (Lemma1245.JJ A K))) := by
  obtain ⟨e, -⟩ := Lemma1245.exists_barOf_equiv_of_cover (p := 3) Nat.prime_three c.jj_le_K c.cover
  exact Lemma1245.isLThreeFour_modCenter_congr e.symm c.hK3

theorem jj_three_dvd : 3 ∣ Nat.card (Lemma1245.JJ A K) := three_dvd_card_of_modCenter c.jj_type

theorem cent_ff_le {x : G} (hx : x ∈ Lemma1245.FF A K) :
    Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G) ≤ Cg x :=
  Sec12b.cent_le_cent_of_mem hx

theorem jj_le_cg {x : G} (hx : x ∈ Lemma1245.FF A K) : Lemma1245.JJ A K ≤ Cg x :=
  c.jj_cent.trans (c.cent_ff_le hx)

theorem jj_comp {x : G} (hx : x ∈ Lemma1245.FF A K) :
    GLAPComponent 3 (Cg x ⊓ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G))
      (Lemma1245.JJ A K) := by
  have hJcomp0 : GLAPComponent 3 (K ⊓ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G))
      (Lemma1245.JJ A K) := by
    refine Claims1245b.glaPComponent_of_normal (Sec12b.layer_le 3 _) ?_
      (fun N₀ O hON hO hle => Claims1245b.layer_le_of_le_sup hO hON hle) c.jj_quasisimple
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Sec12b.layer_le 3 _)).2
      (fun g hg => Lemma1245.mem_normalizer_glaPLayer' (Subgroup.le_normalizer hg))
  have hsn : IsSubnormal (K ⊓ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G))
      (Cg x ⊓ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G)) := by
    have h1 := c.hK.2.1.inf (Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G))
    have e1 : Cg a ⊓ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G) =
        Cg x ⊓ Subgroup.centralizer ((Lemma1245.FF A K : Subgroup G) : Set G) := by
      rw [inf_eq_right.2 (c.cent_ff_le c.a_mem_ff), inf_eq_right.2 (c.cent_ff_le hx)]
    rwa [e1] at h1
  exact l119_glaPComponent_of_isSubnormal Nat.prime_three hsn hJcomp0

theorem a0_elem : IsElemAbelian 3 (E ⊓ A) := Lemma124.isElemAbelian_of_le inf_le_right c.elemAbelian

theorem exists_a0_ne_one : ∃ e ∈ E ⊓ A, e ≠ 1 := by
  have hne : E ⊓ A ≠ ⊥ := by
    intro hbot
    have h9 := c.hA0.1
    rw [hbot, Subgroup.card_bot] at h9
    omega
  obtain ⟨⟨e, he⟩, hne1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  exact ⟨e, he, fun h => hne1 (Subtype.ext h)⟩

theorem a0_isEkIn {x : G} (hx : x ∈ A) : IsEkIn 3 2 (Cg x) (E ⊓ A) :=
  ⟨(inf_le_right : E ⊓ A ≤ A).trans (c.le_cg hx), c.a0_elem, by rw [c.hA0.1]; norm_num⟩

theorem rank_four (h122 : Lemma122_i_iiStatement) (h123 : Lemma123Statement)
    (h117 : Prop117_cex_falseStatement) : CFSG.Open.pRank 3 A = 4 :=
  Lemma1245.pRank_eq_four_of_inputs h122 h123 h117 lemma104_ii_holds lemma104_iii_holds
    lemma104_iv_holds c.h c.hK c.hK3 c.hKM

theorem decomp (hI7 : Input7_L34) (hA4 : CFSG.Open.pRank 3 A = 4) :
    A = (E ⊓ A) ⊔ Lemma1245.FF A K ∧ Nat.card (Lemma1245.FF A K) = 9 := by
  obtain ⟨h1, h2, -⟩ := Lemma1245.decomp_of_normalizes hI7 c.elemAbelian hA4 c.hAN c.quasisimple c.hK3
    (glaPPrimeCore_quotient_eq_bot (p := 3) Nat.prime_three) inf_le_right c.hA0.1
    (Lemma124.inter_disjoint_centBar_of_faithful c.hA0.2)
  exact ⟨h1, h2⟩

theorem tof_cent_le_normalizer (h122 : Lemma122_i_iiStatement) :
    Tof 3 M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨e, he, he1⟩ := c.exists_a0_ne_one
  intro t ht
  have hte : t ∈ Tof 3 M a ⊓ Cg e := ⟨ht.1, Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 ht.2 e he).symm⟩
  have ht2 : t ∈ pCoreOf 2 (Cg2 e a) := (h122 c.h).1 e he he1 hte
  set D : Subgroup G := Subgroup.closure ({e, a} : Set G) with hD
  have hDA : D ≤ A := (Subgroup.closure_le _).2
    (Set.insert_subset_iff.2 ⟨he.2, Set.singleton_subset_iff.2 c.h.ha.1⟩)
  have hD3 : IsPGroup 3 ↥D := (Lemma124.isPGroup_three_of_isElemAbelian c.elemAbelian).to_le hDA
  have hDY : D ≤ Cg a := hDA.trans (c.le_cg c.h.ha.1)
  have hCD : Subgroup.centralizer (D : Set G) = Cg2 e a := Subgroup.centralizer_closure _
  have hCY : Subgroup.centralizer (D : Set G) ≤ Cg a := by
    rw [hCD]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ rfl))
  have h1 := Claims1245b.pCoreOf_two_cent_le_normalizer hD3 hDY hCY c.hK
  rw [hCD] at h1
  exact h1 ht2

theorem exists_unitary (h122 : Lemma122_i_iiStatement) (h122iii : Lemma122_iiiStatement)
    (hdec : A = (E ⊓ A) ⊔ Lemma1245.FF A K) (hF9 : Nat.card (Lemma1245.FF A K) = 9)
    (hVx : Lemma1245.VxClaim) :
    ∃ u ∈ pCoreOf 2 M ⊓ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (Lemma1245.JJ A K : Set G),
        IsUnitaryAut (barAut 3 (Lemma1245.JJ A K) ⟨u, hu⟩) :=
  Lemma1245.exists_unitary_J c.h h122iii ⟨c.ff_le, c.ff_elem, by rw [hF9]; norm_num⟩
    (fun x hx hx1 V hV1 hV2 => hVx c.h c.hK c.hK3 c.hKM c.hA0 c.hAN c.cover hx hx1 hV1 hV2)
    c.cover c.jj_le_K (exists_unitary_cent_A' c.h hdec (c.tof_cent_le_normalizer h122) c.hu₀)

theorem mem_deltaTwo {x u : G} (hx : x ∈ A) (hu : u ∈ pCoreOf 2 M)
    (huA : u ∈ Subgroup.centralizer (A : Set G)) : u ∈ Lemma129.deltaTwo (Cg x) (E ⊓ A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Lemma129.deltaTwo
  refine Subgroup.mem_iInf.2 fun d => Subgroup.mem_iInf.2 fun hd => Subgroup.mem_iInf.2 fun hd1 => ?_
  have hud : u ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 huA d hd.2).symm
  have h1 : u ∈ pCoreOf 2 (alphaOf 3 M ⊓ Subgroup.centralizer ({d} : Set G)) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_inf_right _ (Sec12a.le_alphaOf_two (p := 3) M)) ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left) ⟨hu, hud⟩
    intro g hg
    exact Prop121.normalizer_inf_mem (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
      (Sec12a.alphaOf_le_self (p := 3) M hg.1)) (Subgroup.le_normalizer hg.2)
  have h2 : u ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) :=
    c.h.pair.1.1.2.clause_b d hd.1 hd1 h1
  have hux : u ∈ Cg x :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 huA x hx).symm
  exact Lemma129.inf_pCoreOf_two_le (Cg x) _ ⟨hux, h2⟩

theorem cover_of_component (hI191 : Lemma129.Input19_1_two) (hI1916 : Lemma123.Input19_16_two)
    (hI1417 : Input14_17) (hF9 : Nat.card (Lemma1245.FF A K) = 9)
    {x : G} (hx : x ∈ Lemma1245.FF A K) (hx1 : x ≠ 1)
    {u : G} (huM : u ∈ pCoreOf 2 M) (huA : u ∈ Subgroup.centralizer (A : Set G))
    (huN : u ∈ Subgroup.normalizer (Lemma1245.JJ A K : Set G))
    (hu1 : barAut 3 (Lemma1245.JJ A K) ⟨u, huN⟩ ≠ 1)
    {L : Subgroup G} (hL : GLAPComponent 3 (Cg x) L) (hJL : Lemma1245.JJ A K ≤ L)
    (hFN : Lemma1245.FF A K ≤ Subgroup.normalizer (L : Set G)) :
    barX 3 L (Lemma1245.JJ A K) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxA : x ∈ A := c.ff_le hx
  have hXtop : Cg x ≠ ⊤ := Sec12b.cent_ne_top c.h.standing hx1
  have hXK : CFSG.Open.IsKGroup ↥(Cg x) := isKGroup_of_isKProper c.h.standing.kProper hXtop
  have huX : u ∈ Cg x :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 huA x hxA).symm
  obtain ⟨L', hL', hnc⟩ := exists_not_centralized (𝒞 := {L})
    (fun L₀ hL₀ => (Set.mem_singleton_iff.1 hL₀) ▸ hL.1)
    (le_iSup₂_of_le (f := fun L₀ (_ : L₀ ∈ ({L} : Set (Subgroup G))) => L₀) L (Set.mem_singleton L) hJL)
    (c.jj_le_cg hx) (c.mem_deltaTwo hxA huM huA) huX huN hu1
  rw [Set.mem_singleton_iff] at hL'
  rw [hL'] at hnc
  obtain ⟨hA0N, hfaith, hbal, -⟩ := (hI191 G c.h.standing.kProper 3 Nat.prime_three (by norm_num) (Cg x)
    hXtop 2 (E ⊓ A) (by norm_num) (c.a0_isEkIn hxA)).2 L hL hnc
  obtain ⟨y, hyF, hyx⟩ := exists_not_mem_zpowers c.ff_elem hF9 hx
  have hFxy := eq_zpowers_sup c.ff_elem hF9 hx hx1 hyF hyx
  have hJy : GLAPComponent 3 (Cg x ⊓ Subgroup.centralizer ({y} : Set G)) (Lemma1245.JJ A K) := by
    rw [← inf_centralizer_eq hFxy hyF]
    exact c.jj_comp hx
  have hJyc : Lemma1245.JJ A K ≤ Subgroup.centralizer ({y} : Set G) := hJy.1.trans inf_le_right
  have hJLy : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) (Lemma1245.JJ A K) :=
    glaPComponent_of_le Nat.prime_three hJy (le_inf hJL hJyc) (inf_le_inf_right _ hL.1)
  have hchev := hI1417 (Cg x) L hXK hL y (hFN hyF) (c.ff_elem.2 y hyF) (Lemma1245.JJ A K) hJLy c.jj_type
  have hqL : CFSG.Open.IsQuasisimple (barOf 3 L) := l119_isQuasisimple_barOf (p := 3) Nat.prime_three hL
  have hOL : GLAPPrimeCore 3 (barOf 3 L) = ⊥ := glaPPrimeCore_quotient_eq_bot (p := 3) Nat.prime_three
  have hBel : IsElemAbelian 3 (autBar 3 (E ⊓ A) L) := Lemma129.isElemAbelian_autBar hA0N c.a0_elem
  have hBcard : Nat.card (autBar 3 (E ⊓ A) L) = 3 ^ 2 := by
    rw [Lemma129.card_autBar 3 hA0N hfaith, c.hA0.1]
    norm_num
  obtain ⟨-, hLt, -⟩ := hI1916 3 Nat.prime_three (by norm_num) (barOf 3 L) hqL hOL hchev 2
    (autBar 3 (E ⊓ A) L) le_rfl hBel hBcard hbal
  exact barX_eq_top_of_modCenter hJL hqL hLt c.jj_type

theorem false_of_cycled (hI191 : Lemma129.Input19_1_two) (hI1916 : Lemma123.Input19_16_two)
    (hI1417 : Input14_17) (hNorm : Lemma1245.NormClaim) (hA4 : CFSG.Open.pRank 3 A = 4)
    (hF9 : Nat.card (Lemma1245.FF A K) = 9)
    {x : G} (hx : x ∈ Lemma1245.FF A K) (hx1 : x ≠ 1)
    {u : G} (huM : u ∈ pCoreOf 2 M) (huA : u ∈ Subgroup.centralizer (A : Set G))
    (huN : u ∈ Subgroup.normalizer (Lemma1245.JJ A K : Set G))
    (hu1 : barAut 3 (Lemma1245.JJ A K) ⟨u, huN⟩ ≠ 1)
    {𝒞 : Set (Subgroup G)} (hcomp : ∀ L ∈ 𝒞, GLAPComponent 3 (Cg x) L)
    (hJ𝒞 : Lemma1245.JJ A K ≤ ⨆ L ∈ 𝒞, L)
    (hstab : ∀ L ∈ 𝒞, ∀ e ∈ Lemma1245.FF A K, GLBConj e L ∈ 𝒞)
    (htr : ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, ∃ e ∈ Lemma1245.FF A K, GLBConj e L = L')
    (hcyc : ∃ L ∈ 𝒞, ∃ e ∈ Lemma1245.FF A K, GLBConj e L ≠ L) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxA : x ∈ A := c.ff_le hx
  have hXtop : Cg x ≠ ⊤ := Sec12b.cent_ne_top c.h.standing hx1
  have hXK : CFSG.Open.IsKGroup ↥(Cg x) := isKGroup_of_isKProper c.h.standing.kProper hXtop
  have huX : u ∈ Cg x :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 huA x hxA).symm
  obtain ⟨L, hL𝒞, hnc⟩ := exists_not_centralized (fun L hL => (hcomp L hL).1) hJ𝒞 (c.jj_le_cg hx)
    (c.mem_deltaTwo hxA huM huA) huX huN hu1
  have hL := hcomp L hL𝒞
  obtain ⟨y, hyF, hyL⟩ : ∃ y ∈ Lemma1245.FF A K, GLBConj y L ≠ L := by
    obtain ⟨L₀, hL₀, e, he, hne⟩ := hcyc
    obtain ⟨f, hf, rfl⟩ := htr L₀ hL₀ L hL𝒞
    refine ⟨e, he, fun heq => hne ?_⟩
    have h1 : GLBConj e (GLBConj f L₀) = GLBConj f (GLBConj e L₀) := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj, c.comm (c.ff_le hf) (c.ff_le he)]
    rw [h1] at heq
    exact gLBConj_injective f heq
  have hyA : y ∈ A := c.ff_le hyF
  have hyX : y ∈ Cg x := c.le_cg hxA hyA
  have hy3 : y ^ 3 = 1 := c.ff_elem.2 y hyF
  have hyx : y ∉ Subgroup.zpowers x := fun hy => hyL (gLBConj_eq_of_mem_zpowers hL.1 hy)
  have hFxy := eq_zpowers_sup c.ff_elem hF9 hx hx1 hyF hyx
  set L₂ := GLBConj y L with hL₂
  set L₃ := GLBConj y L₂ with hL₃
  have hL₂𝒞 : L₂ ∈ 𝒞 := hstab L hL𝒞 y hyF
  have hL₃𝒞 : L₃ ∈ 𝒞 := hstab L₂ hL₂𝒞 y hyF
  have hy₃ : GLBConj y L₃ = L := by
    rw [hL₃, hL₂, gLBConj_gLBConj, gLBConj_gLBConj, ← pow_three, hy3, gLBConj_one]
  have h12 : L ≠ L₂ := fun h => hyL h.symm
  have h23 : L₂ ≠ L₃ := fun h => hyL (gLBConj_injective y h).symm
  have h31 : L₃ ≠ L := fun h => by
    have h' := congrArg (GLBConj y) h
    rw [hy₃] at h'
    exact hyL h'.symm
  have hmem : ∀ L' ∈ 𝒞, L' = L ∨ L' = L₂ ∨ L' = L₃ := by
    intro L' hL'
    obtain ⟨f, hf, rfl⟩ := htr L hL𝒞 L' hL'
    have hf' : f ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := hFxy ▸ hf
    obtain ⟨v, hv, w, hw, rfl⟩ := Lemma124.exists_mul_of_mem_sup
      (fun a ha b hb => c.comm (c.ff_le (Subgroup.zpowers_le.2 hx ha))
        (c.ff_le (Subgroup.zpowers_le.2 hyF hb))) hf'
    rw [← gLBConj_gLBConj, gLBConj_eq_of_mem_zpowers hL.1 hv]
    rcases Claims1245.mem_zpowers_of_pow_three hy3 hw with h | h | h
    · left
      rw [h, gLBConj_one]
    · right; left
      rw [h]
    · right; right
      rw [h, ← gLBConj_gLBConj]
  have hJ123 : Lemma1245.JJ A K ≤ L ⊔ L₂ ⊔ L₃ := hJ𝒞.trans (iSup₂_le fun L' hL' => by
    rcases hmem L' hL' with h | h | h <;> rw [h]
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right)
  have hJy : GLAPComponent 3 (Cg x ⊓ Subgroup.centralizer ({y} : Set G)) (Lemma1245.JJ A K) := by
    rw [← inf_centralizer_eq hFxy hyF]
    exact c.jj_comp hx
  have hLt := isLThreeFour_of_cycled hL (hcomp L₂ hL₂𝒞) (hcomp L₃ hL₃𝒞) h12 h23 h31 rfl rfl hy₃ hyX hy3 hJy
    hJ123 c.jj_type
  obtain ⟨hA0N, hfaith, hbal, -⟩ := (hI191 G c.h.standing.kProper 3 Nat.prime_three (by norm_num) (Cg x)
    hXtop 2 (E ⊓ A) (by norm_num) (c.a0_isEkIn hxA)).2 L hL hnc
  have hc1 : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
    ext g
    simp [Subgroup.mem_centralizer_singleton_iff]
  have hL1 : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({(1 : G)} : Set G)) L := by
    rw [hc1, inf_top_eq]
    exact glaPComponent_of_le Nat.prime_three hL le_rfl hL.1
  have hchev := hI1417 (Cg x) L hXK hL 1 (Subgroup.one_mem _) (one_pow 3) L hL1 hLt
  have hqL : CFSG.Open.IsQuasisimple (barOf 3 L) := l119_isQuasisimple_barOf (p := 3) Nat.prime_three hL
  have hOL : GLAPPrimeCore 3 (barOf 3 L) = ⊥ := glaPPrimeCore_quotient_eq_bot (p := 3) Nat.prime_three
  have hBel : IsElemAbelian 3 (autBar 3 (E ⊓ A) L) := Lemma129.isElemAbelian_autBar hA0N c.a0_elem
  have hBcard : Nat.card (autBar 3 (E ⊓ A) L) = 3 ^ 2 := by
    rw [Lemma129.card_autBar 3 hA0N hfaith, c.hA0.1]
    norm_num
  obtain ⟨-, -, -, hBinn, -⟩ := hI1916 3 Nat.prime_three (by norm_num) (barOf 3 L) hqL hOL hchev 2
    (autBar 3 (E ⊓ A) L) le_rfl hBel hBcard hbal
  have hIinn : ∀ b ∈ E ⊓ A, InducesInner 3 L b :=
    Lemma123.inducesInner_of_autBar_le_innerAut hA0N hBinn
  have hIf : ∀ b ∈ E ⊓ A, b ∈ centBar 3 ⊤ L → b = 1 := fun b hb hbc => by
    have h' : b ∈ (E ⊓ A) ⊓ centBar 3 ⊤ L := ⟨hb, hbc⟩
    rw [hfaith] at h'
    exact Subgroup.mem_bot.1 h'
  rcases hNorm c.h c.hK c.hK3 c.hKM c.hA0 hA4 hx hx1 hL hLt hA0N hIinn hIf with hAL | hLM
  · exact hyL (gLBConj_eq_of_mem_normalizer (hAL hyA))
  · have hyM : y ∈ M := c.le_M hyA
    have hMy : GLBConj y M = M := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hyM)
    have hL₂M : L₂ ≤ M := (gLBConj_mono y hLM).trans hMy.le
    have hL₃M : L₃ ≤ M := (gLBConj_mono y hL₂M).trans hMy.le
    have hJM : Lemma1245.JJ A K ≤ M := hJ123.trans (sup_le (sup_le hLM hL₂M) hL₃M)
    exact c.hKM (covers_of_le c.hK c.jj_le_K c.cover hJM)

end KxCtx

theorem kxClaim_of_inputs (h123 : Lemma123Statement) (h117 : Prop117_cex_falseStatement) (hI7 : Input7_L34)
    (h1834 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4)
    (hI191 : Lemma129.Input19_1_two) (hI1916 : Lemma123.Input19_16_two) (hI1417 : Input14_17)
    (hNorm : Lemma1245.NormClaim) (hVx : Lemma1245.VxClaim) : Lemma1245.KxClaim := by
  intro G _ _ m B M E A a h K hK hK3 hKM hu₀ hA0 hAN x hx hx1
  have c : KxCtx G m B M E A a K := ⟨h, hK, hK3, hKM, hu₀, hA0, hAN⟩
  have hA4 := c.rank_four Claims122.lemma122_i_ii_holds h123 h117
  obtain ⟨hdec, hF9⟩ := c.decomp hI7 hA4
  obtain ⟨u, ⟨⟨huM, -⟩, huA⟩, huN, huU⟩ :=
    c.exists_unitary Claims122.lemma122_i_ii_holds Claims122.lemma122_iii_holds hdec hF9 hVx
  have hu1 : barAut 3 (Lemma1245.JJ A K) ⟨u, huN⟩ ≠ 1 := by
    intro h1
    have h2 := huU.1
    rw [h1, orderOf_one] at h2
    norm_num at h2
  have hxA : x ∈ A := c.ff_le hx
  have hXK : CFSG.Open.IsKGroup ↥(Cg x) :=
    isKGroup_of_isKProper h.standing.kProper (Sec12b.cent_ne_top h.standing hx1)
  obtain ⟨𝒞, hcomp, heq, hstab, htr⟩ := h1834 G (Cg x) hXK 3 Nat.prime_three (Lemma1245.FF A K)
    (c.ff_le.trans (c.le_cg hxA)) c.ff_elem (Lemma1245.JJ A K) (c.jj_comp hx)
  have heq' : (⨆ L ∈ 𝒞, L) = Kx 3 (Lemma1245.JJ A K) x := heq
  have hJ𝒞 : Lemma1245.JJ A K ≤ ⨆ L ∈ 𝒞, L := heq' ▸ Sec12b.le_kx x (Lemma1245.JJ A K)
  by_cases hcyc : ∃ L ∈ 𝒞, ∃ e ∈ Lemma1245.FF A K, GLBConj e L ≠ L
  · exact (c.false_of_cycled hI191 hI1916 hI1417 hNorm hA4 hF9 hx hx1 huM huA huN hu1 hcomp hJ𝒞 hstab
      htr hcyc).elim
  push Not at hcyc
  have h𝒞ne : 𝒞.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hJbot : Lemma1245.JJ A K ≤ ⊥ := by simpa [hne] using hJ𝒞
    have h1 : Nat.card (Lemma1245.JJ A K) = 1 := by rw [le_bot_iff.1 hJbot, Subgroup.card_bot]
    have h3 := c.jj_three_dvd
    rw [h1] at h3
    omega
  obtain ⟨L₀, hL₀⟩ := h𝒞ne
  have hall : ∀ L ∈ 𝒞, L = L₀ := fun L hL => by
    obtain ⟨e, he, rfl⟩ := htr L₀ hL₀ L hL
    exact hcyc L₀ hL₀ e he
  have hKx : Kx 3 (Lemma1245.JJ A K) x = L₀ := by
    rw [← heq']
    exact le_antisymm (iSup₂_le fun L hL => (hall L hL).le)
      (le_iSup₂_of_le (f := fun L (_ : L ∈ 𝒞) => L) L₀ hL₀ le_rfl)
  have hJL₀ : Lemma1245.JJ A K ≤ L₀ := hKx ▸ Sec12b.le_kx x (Lemma1245.JJ A K)
  subst hKx
  exact ⟨hcomp _ hL₀, c.cover_of_component hI191 hI1916 hI1417 hF9 hx hx1 huM huA huN hu1 (hcomp _ hL₀)
    hJL₀ fun f hf => mem_normalizer_iff_gLBConj_eq.2 (hcyc _ hL₀ f hf)⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1245c

end

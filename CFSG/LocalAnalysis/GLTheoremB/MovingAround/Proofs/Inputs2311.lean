module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims126b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1314b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop1116Design

section KStar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_le {X K : Subgroup G} (hK : K ≤ X) {x : G} (hx : x ∈ X) : GLBConj x K ≤ X :=
  (gLBConj_mono x hK).trans (gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)).le

omit [Finite G] in
theorem kstar_le {X A0 K : Subgroup G} (hA0 : A0 ≤ X) (hK : K ≤ X) : (⨆ x ∈ A0, GLBConj x K) ≤ X :=
  iSup₂_le fun _ hx => conj_le hK (hA0 hx)

omit [Finite G] in
theorem glaPComponent_conj {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) {x : G} (hx : x ∈ X) :
    GLAPComponent p X (GLBConj x K) := by
  have h := glaPComponent_gLBConj hK x
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)] at h

theorem isSubnormal_kstar {p : ℕ} {X A0 K : Subgroup G} (hK : GLAPComponent p X K) (hA0 : A0 ≤ X) :
    IsSubnormal (⨆ x ∈ A0, GLBConj x K) X := by
  have e : (⨆ x ∈ A0, GLBConj x K) = ⨆ x : ↥A0, GLBConj (x : G) K := by
    refine le_antisymm (iSup₂_le fun x hx => le_iSup_of_le ⟨x, hx⟩ le_rfl)
      (iSup_le fun x => le_iSup₂_of_le (x : G) x.2 le_rfl)
  rw [e]
  exact Claims126b.isSubnormal_iSup_glaPComponent _ fun x => glaPComponent_conj hK (hA0 x.2)

omit [Finite G] in
theorem mem_normalizer_kstar {A0 K : Subgroup G} {x : G} (hx : x ∈ A0) :
    x ∈ Subgroup.normalizer ((⨆ y ∈ A0, GLBConj y K : Subgroup G) : Set G) := by
  have key : ∀ g ∈ A0, GLBConj g (⨆ y ∈ A0, GLBConj y K) ≤ ⨆ y ∈ A0, GLBConj y K := by
    intro g hg
    show (⨆ y ∈ A0, GLBConj y K).map (MulAut.conj g⁻¹).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun y hy => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    show GLBConj g (GLBConj y K) ≤ _
    rw [gLBConj_gLBConj]
    exact le_iSup₂_of_le (y * g) (A0.mul_mem hy hg) le_rfl
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key x hx) ?_
  have h1 := gLBConj_mono x (key x⁻¹ (A0.inv_mem hx))
  rwa [gLBConj_gLBConj_inv] at h1

omit [Finite G] in
theorem kstar_eq_of_le_normalizer {A0 K : Subgroup G} (hN : A0 ≤ Subgroup.normalizer (K : Set G)) :
    (⨆ x ∈ A0, GLBConj x K) = K :=
  le_antisymm (iSup₂_le fun _ hx => (gLBConj_eq_of_mem_normalizer (hN hx)).le)
    (le_iSup₂_of_le (1 : G) A0.one_mem (gLBConj_one K).ge)

omit [Finite G] in
@[expose] def famConj (p : ℕ) (C K : Subgroup G) (A0 : Subgroup ↥C) :
    Set (Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :=
  {Z | ∃ z ∈ A0, Z = GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)}

theorem barX_kstar_eq {p : ℕ} {a : G} {A0 K : Subgroup G} (hK : K ≤ Cg a) (hA0 : A0 ≤ Cg a) :
    barX p (Cg a) (⨆ x ∈ A0, GLBConj x K) = sSup (famConj p (Cg a) K (A0.subgroupOf (Cg a))) := by
  refine le_antisymm
    (Claims1116.barX_iSup₂_le (fun x hx => conj_le hK (hA0 hx)) fun x hx => ?_) (sSup_le ?_)
  · rw [l119_barX_gLBConj (hA0 hx) hK]
    exact le_sSup ⟨⟨x, hA0 hx⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [← l119_barX_gLBConj z.2 hK]
    exact Claims1116.bar_mono (le_iSup₂_of_le (z : G) ((Subgroup.mem_subgroupOf).1 hz) le_rfl)

end KStar

section Facts

variable {G : Type} [Group G] [Finite G]

theorem dvd_card_barX {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K) :
    p ∣ Nat.card (barX p X K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_congr (quotEquivBarX hp hK.1 hK.2.1).toEquiv]
  by_contra hndvd
  have hcop : Nat.Coprime p (Nat.card (barOf p K)) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
  have hO : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) := CFSG.pPrimeCore_coprime_card (p := p)
  have hcard : Nat.card ↥K = Nat.card (barOf p K) * Nat.card (GLAPPrimeCore p ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore p ↥K)
  exact not_coprime_card_of_pComponent hp hK (by rw [hcard]; exact Nat.Coprime.mul_right hcop hO)

theorem centralizes_of_mem_centBar {p : ℕ} (hp : p.Prime) {a z : G} {K : Subgroup G}
    (hK : GLAPComponent p (Cg a) K) (hzC : z ∈ Cg a) (hz : z ∈ centBar p ⊤ K) :
    ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨z, hzC⟩ * q =
      q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨z, hzC⟩ := by
  obtain ⟨γ, hγ, hγz⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hz).1
  have hγz' : (γ : G) = z := hγz
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := hγz' ▸ γ.2
  have hbar : barAut p K ⟨z, hzN⟩ = 1 := by
    have : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (K : Set G))) = γ := Subtype.ext hγz'.symm
    rw [this]
    exact MonoidHom.mem_ker.1 hγ
  exact l119_centralizes_of_barAut hp hK hzC hzN hbar

end Facts

section Lift

variable {G : Type} [Group G] [Finite G]

theorem core_le {p : ℕ} (hp : p.Prime) {a : G} {L : Subgroup G} (hLC : L ≤ Cg a)
    (hLsn : IsSubnormal L (Cg a)) {z : ↥(Cg a)} (hzN : (z : G) ∈ Subgroup.normalizer (L : Set G))
    (hzp : IsPGroup p (Subgroup.zpowers (z : G))) :
    GLAPPrimeCoreOf p (barX p (Cg a) L ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ≤
      barX p (Cg a) (GLAPPrimeCoreOf p (Cg2 (z : G) a)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have heq := barX_inf_centralizer hp z.2 hLC hzN hzp
  rw [← heq]
  refine (Claims1314b.core_barX_le (inf_le_left.trans hLC)).trans (Claims1116.bar_mono ?_)
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer ({(z : G)} : Set G)) (Cg2 (z : G) a) := by
    unfold Cg2
    rw [l119_cg2_eq]
    exact isSubnormal_inf hLsn _
  exact glaPPrimeCoreOf_le_of_isSubnormal hp hsub

theorem exists_lift {p q : ℕ} (hp : p.Prime) {a : G} {L : Subgroup G} (hLC : L ≤ Cg a)
    (hLsn : IsSubnormal L (Cg a)) {z : ↥(Cg a)} (hzN : (z : G) ∈ Subgroup.normalizer (L : Set G))
    (hzp : IsPGroup p (Subgroup.zpowers (z : G))) {Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))}
    (hQ : GLAPComponent p (barX p (Cg a) L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q)
    (hQchev : IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))) :
    ∃ P : Subgroup G, GLAPComponent p (Cg2 (z : G) a) P ∧ P ≤ L ∧
      IsChevSimple q (barOf p P ⧸ Subgroup.center (barOf p P)) ∧ barX p (Cg a) P = Q := by
  obtain ⟨P, hP, hPQ⟩ := exists_glaPComponent_lift hp z.2 hLC hzN hzp hQ
  have hPL : P ≤ L := hP.1.trans inf_le_left
  have hPC : P ≤ Cg a := hPL.trans hLC
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer ({(z : G)} : Set G)) (Cg2 (z : G) a) := by
    unfold Cg2
    rw [l119_cg2_eq]
    exact isSubnormal_inf hLsn _
  have hPc : GLAPComponent p (Cg2 (z : G) a) P := l119_glaPComponent_of_isSubnormal hp hsub hP
  have hPq : CFSG.Open.IsQuasisimple (↥P ⧸ GLAPPrimeCore p ↥P) := l119_isQuasisimple_barOf hp hP
  have hQq : CFSG.Open.IsQuasisimple (↥Q ⧸ GLAPPrimeCore p ↥Q) := l119_isQuasisimple_barOf hp hQ
  have hf : ((QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a))).comp (Subgroup.inclusion hPC)).range = Q :=
    (l119_range_eq hPC).trans hPQ
  obtain ⟨eQP⟩ := l119_barOf_centre_iso hp _ hf hPq hQq
  exact ⟨P, hPc, hPL, Claims1116.isChevSimple_congr eQP hQchev, hPQ⟩

end Lift

section Bad

variable {G : Type} [Group G] [Finite G]

theorem gen_of_bad {p q : ℕ} (hp : p.Prime) {a : G} {K E A : Subgroup G}
    (hK : GLAPComponent p (Cg a) K)
    (hchev : IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K)))
    (hA0C : E ⊓ A ≤ Cg a) (hA0el : IsElemAbelian p (E ⊓ A))
    (hA0r : 2 ≤ CFSG.Open.pRank p (E ⊓ A))
    (hbad : ∃ z ∈ E ⊓ A, z ≠ 1 ∧ (z ∉ Subgroup.normalizer (K : Set G) ∨ z ∈ centBar p ⊤ K)) :
    barX p (Cg a) (⨆ x ∈ E ⊓ A, GLBConj x K) ≤
      ⨆ (e : G) (_ : e ∈ E ⊓ A) (_ : e ≠ 1),
        (barX p (Cg a) (GLAPPrimeCoreOf p (Cg2 e a)) ⊔
          ⨆ (J : Subgroup G) (_ : GLAPComponent p (Cg2 e a) J ∧
              J ≤ (⨆ x ∈ E ⊓ A, GLBConj x K) ∧
              IsChevSimple q (barOf p J ⧸ Subgroup.center (barOf p J))),
            barX p (Cg a) J) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z₀, hz₀A, hz₀1, hz₀bad⟩ := hbad
  set A0 : Subgroup G := E ⊓ A with hA0
  set Kstar : Subgroup G := ⨆ x ∈ A0, GLBConj x K with hKstar
  have hAcomm : ∀ x ∈ A0, ∀ y ∈ A0, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA0el.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A0, x ^ p = 1 := fun x hx => hA0el.2 x hx
  set A0C : Subgroup ↥(Cg a) := A0.subgroupOf (Cg a) with hA0Cdef
  set Bbar : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) :=
    A0C.map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a))) with hBbar
  set Kb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := barX p (Cg a) K with hKb
  set 𝓛 := famConj p (Cg a) K A0C with h𝓛def
  set Yb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := sSup 𝓛 with hYb
  have hKbmem : Kb ∈ 𝓛 := ⟨1, A0C.one_mem, by rw [map_one, gLBConj_one]⟩
  have h𝓛c : ∀ X ∈ 𝓛, IsComponentOf X ⊤ := by
    rintro _ ⟨z, -, rfl⟩
    exact l119_conj_component hK z
  have hcomm𝓛 : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
    rintro X ⟨w, -, rfl⟩ X' ⟨w', -, rfl⟩ hne x hx y hy
    exact l119_conj_comm hK hne hx hy
  have hYcomp : ∀ X ∈ 𝓛, IsComponentOf X Yb := fun X hX => l119_isComponentOf_sSup h𝓛c hcomm𝓛 hX
  have hBcomm : ∀ z ∈ A0C, ∀ w ∈ A0C,
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w =
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w *
          QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z := by
    intro z hz w hw
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hAcomm _ ((Subgroup.mem_subgroupOf).1 hz) _ ((Subgroup.mem_subgroupOf).1 hw)
  have hKsC : Kstar ≤ Cg a := kstar_le hA0C hK.1
  have hKsn : IsSubnormal Kstar (Cg a) := isSubnormal_kstar hK hA0C
  have hYbar : barX p (Cg a) Kstar = Yb := barX_kstar_eq hK.1 hA0C
  have hBnorm : Bbar ≤ Subgroup.normalizer ((Yb : Subgroup _) : Set _) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_normalizer_iff_gLBConj_eq, ← hYbar, ← l119_barX_gLBConj z.2 hKsC]
    exact congrArg (barX p (Cg a))
      (mem_normalizer_iff_gLBConj_eq.1 (mem_normalizer_kstar (Subgroup.mem_subgroupOf.1 hz)))
  have hA0Cel : IsElemAbelian p A0C := l119_isElemAbelian_subgroupOf hA0el (Cg a)
  have hBel : IsElemAbelian p Bbar := CFSG.SectionRank.isElemAbelian_map hA0Cel _
  have hB_rank : 2 ≤ CFSG.Open.pRank p Bbar := le_trans hA0r (l119_pRank_image_ge hp hA0C hA0el)
  have hpY : p ∣ Nat.card ↥Yb :=
    dvd_trans (dvd_card_barX hp hK) (Subgroup.card_dvd_of_le (le_sSup hKbmem))
  have htrans : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, ∃ b ∈ Bbar, GLBConj b X = X' := by
    rintro X ⟨w, hw, rfl⟩ X' ⟨w', hw', rfl⟩
    exact ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (w⁻¹ * w'),
      Subgroup.mem_map_of_mem _ (A0C.mul_mem (A0C.inv_mem hw) hw'), l119_conj_trans w w'⟩
  set z₀C : ↥(Cg a) := ⟨z₀, hA0C hz₀A⟩ with hz₀Cdef
  have hz₀C : z₀C ∈ A0C := Subgroup.mem_subgroupOf.2 hz₀A
  have hb₀B : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀C ∈ Bbar := Subgroup.mem_map_of_mem _ hz₀C
  have hz₀pow : z₀C ^ p = 1 := by
    apply Subtype.ext
    simpa using hApow _ hz₀A
  have hb₀1 : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀C ≠ 1 := by
    intro h
    apply hz₀1
    have h2 := l119_eq_one_of_pow_of_mem_core hp hz₀pow ((QuotientGroup.eq_one_iff _).1 h)
    exact congrArg Subtype.val h2
  have hJb₀ : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀C ∈ Subgroup.centralizer (Yb : Set _) ∨
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀C ∉ Subgroup.normalizer (Kb : Set _) := by
    rcases hz₀bad with hN | hC
    · right
      intro hb
      exact hN (l119_mem_normalizer_of_bar hp hK z₀C hb)
    · left
      have hC' := centralizes_of_mem_centBar hp hK (hA0C hz₀A) hC
      have hYc : Yb ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀C} : Set _) := by
        refine sSup_le fun X hX => ?_
        obtain ⟨w, hw, rfl⟩ := hX
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact l119_centralizes_gLBConj (hBcomm z₀C hz₀C w hw) hC' x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h2 := hYc hh
      rw [Subgroup.mem_centralizer_iff] at h2
      exact (h2 _ (Set.mem_singleton _)).symm
  have hI22' := input22_3_2_holds (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Bbar Yb Kb 𝓛 hBel hBnorm
    hKbmem hB_rank hpY rfl hYcomp hcomm𝓛 htrans
    ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀C, hb₀B, hb₀1, hJb₀⟩
  rw [hYbar, hI22']
  refine sSup_le ?_
  rintro Z ⟨b, hb, hb1, hJ, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hb
  have hzA : (z : G) ∈ A0 := Subgroup.mem_subgroupOf.1 hz
  have hz1 : (z : G) ≠ 1 := by
    intro h
    apply hb1
    have hzeq : z = 1 := Subtype.ext h
    rw [hzeq, map_one]
  have hzpow : (z : G) ^ p = 1 := hApow _ hzA
  have hzp : IsPGroup p (Subgroup.zpowers (z : G)) := l119_isPGroup_zpowers hzpow
  have hzpow' : z ^ p = 1 := by
    apply Subtype.ext
    simpa using hzpow
  have hbord : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) = p := by
    apply orderOf_eq_prime
    · rw [← map_pow, hzpow', map_one]
    · exact hb1
  have hdich : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z ∈ Subgroup.centralizer (Yb : Set _) ∨
      ∀ X ∈ 𝓛, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z ∉ Subgroup.normalizer (X : Set _) := by
    rcases hJ with hC | hN
    · exact Or.inl hC
    · right
      rintro X ⟨w, hw, rfl⟩ hmem
      exact hN ((l119_normalizer_gLBConj_iff (hBcomm z hz w hw) Kb).1 hmem)
  unfold GLAPLayer
  refine sSup_le fun Q hQ => ?_
  obtain ⟨X₀, hX₀, ⟨e0⟩⟩ := input18_3_diag_holds (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Yb 𝓛
    (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) hbord (hBnorm (Subgroup.mem_map_of_mem _ hz)) rfl
    hYcomp hcomm𝓛 hdich Q hQ
  obtain ⟨w, -, rfl⟩ := hX₀
  have eK : ↥(GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w) Kb) ≃* ↥Kb :=
    (l119_gLBConj_equiv _ Kb).symm
  have hKbe : barOf p K ≃* ↥Kb := quotEquivBarX hp hK.1 hK.2.1
  have eQK : (barOf p Q ⧸ Subgroup.center (barOf p Q)) ≃* (barOf p K ⧸ Subgroup.center (barOf p K)) :=
    (e0.trans (l119_centerQuot_equiv eK)).trans (l119_centerQuot_equiv hKbe).symm
  have hQchev : IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q)) :=
    Claims1116.isChevSimple_congr eQK.symm hchev
  have hQ' : GLAPComponent p (barX p (Cg a) Kstar ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q := by
    rw [hYbar]
    exact hQ
  obtain ⟨P, hPc, hPK, hPchev, hPQ⟩ :=
    exists_lift hp hKsC hKsn (mem_normalizer_kstar hzA) hzp hQ' hQchev
  rw [← hPQ]
  refine le_iSup₂_of_le (z : G) hzA (le_iSup_of_le hz1 (le_sup_of_le_right ?_))
  exact le_iSup₂_of_le P ⟨hPc, hPK, hPchev⟩ le_rfl

end Bad

@[expose] def Input23_11GenFaithful : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K)) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) →
      ¬ Prop1116Iii p q E A K →
      barX p (Cg a) K ≤
        ⨆ (e : G) (_ : e ∈ E ⊓ A) (_ : e ≠ 1),
          (barX p (Cg a) (GLAPPrimeCoreOf p (Cg2 e a)) ⊔
            ⨆ (J : Subgroup G) (_ : GLAPComponent p (Cg2 e a) J ∧ J ≤ K ∧
                IsChevSimple q (barOf p J ⧸ Subgroup.center (barOf p J))),
              barX p (Cg a) J)

theorem input23_11Gen_of_faithful (h : Input23_11GenFaithful) : Claims1116.Input23_11Gen := by
  intro G _ _ p q hp hp2 hq hq2 hqp a K E A hK hchev hA0C hA0el hA0r hIii
  by_cases hbad : ∃ z ∈ E ⊓ A, z ≠ 1 ∧ (z ∉ Subgroup.normalizer (K : Set G) ∨ z ∈ centBar p ⊤ K)
  · exact gen_of_bad hp hK hchev hA0C hA0el hA0r hbad
  · have hN : E ⊓ A ≤ Subgroup.normalizer (K : Set G) := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · by_contra hxN
        exact hbad ⟨x, hx, hx1, Or.inl hxN⟩
    have hF : ∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1 := by
      intro x hx hxc
      by_contra hx1
      exact hbad ⟨x, hx, hx1, Or.inr hxc⟩
    rw [kstar_eq_of_le_normalizer hN]
    exact h hp hp2 hq hq2 hqp hK hchev hA0C hA0el hA0r hN hF hIii

@[expose] def Input23_11Bar : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K)) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) →
      ¬ Prop1116Iii p q E A K →
      barX p (Cg a) K ≤
        ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
          (GLAPPrimeCoreOf p (barX p (Cg a) K ⊓ Subgroup.centralizer
              ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} :
                Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ⊔
            ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
              (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
                  ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} :
                    Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
                IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))),
              Q)

theorem input23_11GenFaithful_of_bar (h : Input23_11Bar) : Input23_11GenFaithful := by
  intro G _ _ p q hp hp2 hq hq2 hqp a K E A hK hchev hA0C hA0el hA0r hN hF hIii
  refine (h hp hp2 hq hq2 hqp hK hchev hA0C hA0el hA0r hN hF hIii).trans ?_
  refine iSup_le fun z => iSup_le fun hzA => iSup_le fun hz1 => ?_
  have hz1' : (z : G) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hzN : (z : G) ∈ Subgroup.normalizer (K : Set G) := hN hzA
  have hzp : IsPGroup p (Subgroup.zpowers (z : G)) := l119_isPGroup_zpowers (hA0el.2 _ hzA)
  refine le_trans ?_ (le_iSup₂_of_le (z : G) hzA (le_iSup_of_le hz1' le_rfl))
  refine sup_le_sup (core_le hp hK.1 hK.2.1 hzN hzp) (iSup₂_le fun Q hQ => ?_)
  obtain ⟨P, hPc, hPK, hPchev, hPQ⟩ := exists_lift hp hK.1 hK.2.1 hzN hzp hQ.1 hQ.2
  rw [← hPQ]
  exact le_iSup₂_of_le P ⟨hPc, hPK, hPchev⟩ le_rfl

theorem input23_11Gen_of_bar (h : Input23_11Bar) : Claims1116.Input23_11Gen :=
  input23_11Gen_of_faithful (input23_11GenFaithful_of_bar h)

@[expose] def Input23_11Thm4 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K)) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) →
      ¬ Prop1116Iii p q E A K →
      barX p (Cg a) K ≤
        ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
          CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
            ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))))

@[expose] def Input14_2Struct : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K)) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) →
      ¬ Prop1116Iii p q E A K →
      (∀ z : ↥(Cg a), (z : G) ∈ E ⊓ A → z ≠ 1 →
        CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
            ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ≤
          GLAPPrimeCoreOf p (barX p (Cg a) K ⊓ Subgroup.centralizer
              ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} :
                Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ⊔
            ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
              (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
                  ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} :
                    Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
                IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))),
              Q) ∨
      barX p (Cg a) K ≤
        ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
          ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
            (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
                ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} :
                  Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
              IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))),
            Q

theorem input23_11Bar_of_thm4 (h4 : Input23_11Thm4) (hs : Input14_2Struct) : Input23_11Bar := by
  intro G _ _ p q hp hp2 hq hq2 hqp a K E A hK hchev hA0C hA0el hA0r hN hF hIii
  rcases hs hp hp2 hq hq2 hqp hK hchev hA0C hA0el hA0r hN hF hIii with hst | hlay
  · refine (h4 hp hp2 hq hq2 hqp hK hchev hA0C hA0el hA0r hN hF hIii).trans ?_
    exact iSup_mono fun z => iSup_mono fun hzA => iSup_mono fun hz1 => hst z hzA hz1
  · exact hlay.trans (iSup_mono fun z => iSup_mono fun _ => iSup_mono fun _ => le_sup_right)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311

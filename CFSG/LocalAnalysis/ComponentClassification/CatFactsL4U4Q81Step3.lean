module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81E8
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma43

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Q81

theorem mk_ne_mk {G : Type} [Group G] {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N))
    {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (hne : a ≠ b) :
    (QuotientGroup.mk a : G ⧸ N) ≠ QuotientGroup.mk b := by
  intro h1
  have h2 : a⁻¹ * b ∈ N := QuotientGroup.eq.mp h1
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have h3 : (a⁻¹ * b) ^ 2 = 1 := by
    rw [hai, sq, show a * b * (a * b) = a * (b * a) * b by group, ← hab,
      show a * (a * b) * b = (a * a) * (b * b) by group, ha, hb, one_mul]
  have h4 := Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N h2)
  have h5 : orderOf (a⁻¹ * b) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h3) with h6 | h6
    · exact h6
    · rw [h6] at h4
      exact absurd h4 (by decide)
  rw [orderOf_eq_one_iff, inv_mul_eq_one] at h5
  exact hne h5

theorem mem_normalizer_center {G : Type} [Group G] {W : Subgroup G} {g : G}
    (hg : g ∈ normalizer (W : Set G)) :
    g ∈ normalizer ((W ⊓ centralizer (W : Set G) : Subgroup G) : Set G) := by
  have key : ∀ x : G, x ∈ normalizer (W : Set G) → ∀ y ∈ W ⊓ centralizer (W : Set G),
      x * y * x⁻¹ ∈ W ⊓ centralizer (W : Set G) := by
    intro x hx y hy
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hx y).mp (mem_inf.mp hy).1,
      mem_centralizer_iff.mpr fun a ha => ?_⟩
    have ha' : x⁻¹ * a * x ∈ W := by
      have := (mem_normalizer_iff.mp (inv_mem hx) a).mp ha
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.mp (mem_inf.mp hy).2 _ ha'
    calc a * (x * y * x⁻¹) = x * ((x⁻¹ * a * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * a * x)) * x⁻¹ := by rw [h1]
      _ = x * y * x⁻¹ * a := by group
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h1

end Q81

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Standing.Setup42

variable {h : Standing t L 3 4} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

omit [Finite X] in
theorem beta_mem_T (hσ : Setup42 h hS w z) (i j : ℕ) :
    w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
  mul_mem (mul_mem (mem_sup_right (pow_mem (mem_zpowers w) _))
    (pow_mem (mem_sup_left (mem_sup_left (mem_zpowers t))) i))
    (pow_mem (mem_sup_left (mem_sup_right hσ.z_mem)) j)

theorem T_le_centralizer_z (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤
      centralizer ({z} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} := by
  intro x hx
  refine mem_inf.mpr ⟨?_, (mem_inf.mp ((hσ.isSylowOf_T_M hKC i j).le hx)).2⟩
  have hzc := (mem_inf.mp (hσ.X_le_center_T
    (subset_closure (by simp : z ∈ ({t, w ^ (orderOf w / 2), z} : Set X))))).2
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc x hx)

theorem card_closure_beta_z (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    Nat.card (closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) = 4 := by
  have hcl : (closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) =
      zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z := by
    rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hzβ := hσ.z_mem_centralizer_beta hFC hKC i j
  have hc : ∀ a ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j), a * z = z * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (show Commute (w ^ (orderOf w / 2) * t ^ i * z ^ j) z from
      (mem_centralizer_singleton_iff.mp hzβ).symm) n).eq
  have hzn : z ∉ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
    intro h1
    rcases Q81.eq_one_or_eq_of_mem_zpowers_two (hσ.orderOf_beta i j) h1 with h2 | h2
    · exact hσ.z_ne_one h2
    · exact hσ.z_ne_beta i j h2
  rw [hcl, Lemma47.card_sup_zpowers hc hσ.z_order hzn, Nat.card_zpowers, hσ.orderOf_beta i j]

variable {hσ : Setup42 h hS w z} {i j : ℕ}

theorem Q81Data.not_isSylowOf_T (hD : Q81Data hσ i j) (hF : L4U4ThreeInvolutionFacts)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hKG : AutPSL2SylowInput) :
    ¬ IsSylowOf 2 (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
      (centralizer ({z} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) := by
  intro hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzβ := hσ.z_mem_centralizer_beta hFC hKC i j
  have htβ := hσ.t_mem_centralizer_beta i j
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer
      ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hz'2 : (⟨z, hzβ⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) *
      ⟨z, hzβ⟩ = 1 := Subtype.ext (by
    change z * z = 1
    rw [← sq, ← hσ.z_order, pow_orderOf_eq_one])
  have hz2 := hσ.orderOf_mk_z hFC hKC i j
  obtain ⟨X₁, X₂, -, h₁, h₂, hc, hi, hX₁, hX₂, hO⟩ := hD.exists_sl2_z hF hFC hKC
  obtain ⟨E, hE, hEe, hE8⟩ := Q81.exists_elemTwo_eight hc hi hz2 hX₁ hX₂
  have hAsub : (centralizer ({z} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}).subgroupOf
        (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) =
      centralizer {(⟨z, hzβ⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
        Set X)))} := by
    rw [← map_subtype_centralizer hzβ, subgroupOf,
      comap_map_eq_self_of_injective (subtype_injective _)]
  have hTbar := isSylowOf_map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
    ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) (Q81.isSylowOf_subgroupOf hT inf_le_right)
  rw [hAsub, map_centralizer_eq hodd hz'2] at hTbar
  have hEC : E ≤ centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} :=
    hE.trans (sup_le (h₁.trans inf_le_right) (h₂.trans inf_le_right))
  obtain ⟨P', hP', hEP'⟩ := Q81.exists_isSylowOf_ge (RankFour.isPGroup_of_isElemTwo hEe) hEC
  obtain ⟨k, hk, hkP⟩ := L415.exists_map_conj hTbar hP'
  set E' := E.map (MulAut.conj k⁻¹).toMonoidHom with hE'
  have hE'T : E' ≤ ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).subgroupOf
      (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
          ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hEP' hx
    rw [hkP] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show k⁻¹ * (k * y * k⁻¹) * k = y by group]
    exact hy
  have hE'X : E' ≤ X₁ ⊔ X₂ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Q81.oddPart (centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}) := by rw [hO]; exact hE hx
    have hkN := Q81.mem_normalizer_oddPart (Subgroup.le_normalizer (inv_mem hk))
    rw [← hO]
    exact (mem_normalizer_iff.mp hkN x).mp hx'
  have hE'e : GrSLit.IsElemTwo E' := RankFour.isElemTwo_map _ hEe
  have hE'8 : Nat.card E' = 8 := by
    rw [hE', card_map_of_injective (MulAut.conj k⁻¹).injective, hE8]
  have hE't : E' ≤ centralizer {hσ.tBar i j} := by
    refine hE'T.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxt : (x : X) * t = t * x :=
      mem_centralizer_singleton_iff.mp ((mem_inf.mp ((hσ.isSylowOf_T_M hKC i j).le hx)).1)
    rw [mem_centralizer_singleton_iff]
    have htb : hσ.tBar i j = QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
        ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ⟨t, htβ⟩ := rfl
    rw [htb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxt
  have hbb2 : orderOf (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 2 := by
    refine orderOf_eq_prime ?_ (hσ.betaBar_ne_one i j)
    rw [betaBar, ← QuotientGroup.mk_pow]
    have h1 := pow_orderOf_eq_one (w ^ (orderOf w / 2) * t ^ i * z ^ j)
    rw [hσ.orderOf_beta i j] at h1
    have : (⟨_, mem_centralizer_singleton_iff.mpr rfl⟩ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact h1)
    rw [this, QuotientGroup.mk_one]
  have hbbZ := betaBar_mem_center (w ^ (orderOf w / 2) * t ^ i * z ^ j)
  have hbbE' : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∉ E' := by
    intro hb
    have h1 := Q81.mem_zpowers_of_mem_center_sup hc hi hz2 hX₁ hX₂ (hE'X hb)
      (fun x _ => (mem_center_iff.mp hbbZ x).symm)
    rcases Q81.eq_one_or_eq_of_mem_zpowers_two hz2 h1 with h2 | h2
    · exact hσ.betaBar_ne_one i j h2
    · have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j)
          = 1 := by
        have h3 := pow_orderOf_eq_one (w ^ (orderOf w / 2) * t ^ i * z ^ j)
        rw [hσ.orderOf_beta i j, sq] at h3
        exact h3
      set b' : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :=
        ⟨_, mem_centralizer_singleton_iff.mpr rfl⟩ with hb'
      set z' : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :=
        ⟨z, hzβ⟩ with hz'
      exact Q81.mk_ne_mk hodd (a := b') (b := z') (Subtype.ext hβ2) hz'2
        (Subtype.ext (mem_centralizer_singleton_iff.mp hzβ).symm)
        (fun h3 => hσ.z_ne_beta i j (congrArg Subtype.val h3).symm) h2
  obtain ⟨I, hI⟩ := Q81.exists_isInnDiag hD.quasisimple hD.center_cases
  have htbE' : hσ.tBar i j ∉ (E' ⊔ zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Subgroup _) := by
    intro ht
    refine hD.graph I hI (sup_le (hE'X.trans (sup_le ((h₁.trans inf_le_left).trans hI.le)
      ((h₂.trans inf_le_left).trans hI.le))) ?_ ht)
    rw [zpowers_le]
    exact hI.centralizer_le (Subgroup.center_le_centralizer _ hbbZ)
  obtain ⟨E₃, hE₃t, hE₃, hE₃c⟩ := Q81.exists_elemTwo_thirtyTwo_of hbbZ hbb2
    (hσ.orderOf_tBar i j) hE'e hE'8 hE't hbbE' htbE'
  have hle := h.card_le_sixteen_of_le_centralizer_bar hKG htβ hE₃t hE₃
  omega

theorem Q81Data.exists_W (hD : Q81Data hσ i j) (hF : L4U4ThreeInvolutionFacts)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hKG : AutPSL2SylowInput) :
    ∃ W : Subgroup X, IsSylowOf 2 W (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ∧
      IsSylowOf 2 W (centralizer ({z} : Set X) ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ∧
      zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W ∧ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≠ W ∧
      W ⊓ centralizer (W : Set X) = closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTA := hσ.T_le_centralizer_z hKC i j
  have hTS := hσ.isSylowOf_T_M hKC i j
  obtain ⟨W, hW, hTW⟩ := Q81.exists_isSylowOf_ge hTS.isPGroup hTA
  have hTne : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≠ W := fun h1 =>
    hD.not_isSylowOf_T hF hFC hKC hKG (h1 ▸ hW)
  have hWA := hW.le
  have hWt : W ⊓ centralizer {t} = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    refine hTS.eq_of_le (le_inf hTW fun x hx => (mem_inf.mp (hTS.le hx)).1) (fun x hx =>
      mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (hWA (mem_inf.mp hx).1)).2⟩)
      (hW.isPGroup.to_le inf_le_left)
  have htW : t ∈ W := hTW (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hZT : W ⊓ centralizer (W : Set X) ≤ closure {t, w ^ (orderOf w / 2), z} := by
    rw [← hσ.center_T]
    intro x hx
    obtain ⟨hxW, hxc⟩ := mem_inf.mp hx
    have hxt : x ∈ W ⊓ centralizer {t} := mem_inf.mpr ⟨hxW,
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxc t htW).symm⟩
    rw [hWt] at hxt
    exact mem_inf.mpr ⟨hxt, mem_centralizer_iff.mpr fun y hy =>
      mem_centralizer_iff.mp hxc y (hTW hy)⟩
  have hβZ : closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} ≤ W ⊓ centralizer (W : Set X) := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact mem_inf.mpr ⟨hTW (hσ.beta_mem_T i j), mem_centralizer_iff.mpr fun y hy =>
        mem_centralizer_singleton_iff.mp (mem_inf.mp (hWA hy)).2⟩
    · exact mem_inf.mpr ⟨hTW (mem_sup_left (mem_sup_right hσ.z_mem)),
        mem_centralizer_iff.mpr fun y hy =>
          mem_centralizer_singleton_iff.mp (mem_inf.mp (hWA hy)).1⟩
  have htZ : t ∉ W ⊓ centralizer (W : Set X) := by
    intro htZ
    apply hTne
    rw [← hWt]
    refine inf_eq_left.mpr fun x hx => ?_
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (mem_inf.mp htZ).2 x hx)
  have hZ : W ⊓ centralizer (W : Set X) = closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} := by
    have h8 := hσ.card_X
    have h4 := hσ.card_closure_beta_z hFC hKC i j
    have hd1 : Nat.card ↥(W ⊓ centralizer (W : Set X)) ∣ 8 := h8 ▸ card_dvd_of_le hZT
    have hd2 : 4 ∣ Nat.card ↥(W ⊓ centralizer (W : Set X)) := h4 ▸ card_dvd_of_le hβZ
    have hne8 : Nat.card ↥(W ⊓ centralizer (W : Set X)) ≠ 8 := by
      intro h1
      have h2 := eq_of_le_of_card_ge hZT (by rw [h1, h8])
      apply htZ
      rw [h2]
      exact subset_closure (by simp)
    have h44 : Nat.card ↥(W ⊓ centralizer (W : Set X)) = 4 := by
      have hle : Nat.card ↥(W ⊓ centralizer (W : Set X)) ≤ 8 := Nat.le_of_dvd (by norm_num) hd1
      have hpos : 0 < Nat.card ↥(W ⊓ centralizer (W : Set X)) := Nat.card_pos
      obtain ⟨m, hm⟩ := hd2
      rw [hm] at hle hne8 hpos ⊢
      have hm' : m = 1 ∨ m = 2 := by omega
      rcases hm' with rfl | rfl
      · rfl
      · exact absurd rfl hne8
    exact (eq_of_le_of_card_ge hβZ (by rw [h44, h4])).symm
  refine ⟨W, Q81.isSylowOf_of_normalizer_le hW inf_le_right ?_, hW, hTW, hTne, hZ⟩
  intro g hg
  obtain ⟨hgM, hgN⟩ := mem_inf.mp hg
  have hgZ := Q81.mem_normalizer_center hgN
  rw [hZ] at hgZ
  have hgz := hD.conj_z_eq_of_normalizes hF hFC hKC hgZ
  refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hgM⟩
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [hgz]

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit

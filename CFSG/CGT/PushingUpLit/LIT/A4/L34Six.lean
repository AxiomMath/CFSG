module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Star

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4

variable {G : Type} [Group G]

theorem Blk3.eq_one_of_centralizes {X : Subgroup G} {a : G} (hb : Blk3 X a) {w : G}
    (hw : w ∈ pCoreOf 2 X) (hc : ∀ x ∈ X, w * x = x * w) : w = 1 := by
  apply hb.fix w hw
  calc a * w * a⁻¹ = (w * a) * a⁻¹ := by rw [← hc a hb.mem]
    _ = w := by group

theorem stab_bound [Finite G] {X : Subgroup G} {a : G} (hb : Blk3 X a) {S : Subgroup G}
    (hS2 : ∀ s ∈ S, s * s = 1) (hScomm : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s)
    (hSn : ∀ s ∈ S, conjSub s X = X)
    (hSc : ∀ s ∈ S, s ≠ 1 → ¬ ∀ x ∈ X, s * x = x * s) : Nat.card S ≤ 4 := by
  have hSp : IsPGroup 2 ↥S := fun s => ⟨1, Subtype.ext (by simpa [pow_two] using hS2 s.1 s.2)⟩
  have hSnV : ∀ s ∈ S, ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ ∈ pCoreOf 2 X :=
    fun s hs w hw => conj_mem_pCoreOf (hSn s hs) hw
  have hcard := card_le_two_mul_card_centralizer hb hSp hSnV
  set C : Subgroup G := Subgroup.centralizer (pCoreOf 2 X : Set G) ⊓ S with hC
  have hCS : ∀ c ∈ C, c ∈ S ∧ ∀ y ∈ pCoreOf 2 X, c * y = y * c := fun c hc =>
    ⟨(Subgroup.mem_inf.1 hc).2, fun y hy =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).1 y hy).symm⟩
  have hw : ∀ c : ↥C, ∃ w ∈ pCoreOf 2 X, ∀ x ∈ X, (w * (c : G)) * x = x * (w * (c : G)) := fun c =>
    Blk3.exists_correction hb (hSn c (hCS c c.2).1) (hCS c c.2).2
  choose f hfV hfc using hw
  have hmemC : ∀ (c : ↥C) (x : G), x ∈ X → (f c * (c : G)) * x = x * (f c * (c : G)) :=
    fun c x hx => hfc c x hx
  have hcentX : ∀ (c : ↥C), f c * (c : G) ∈ Subgroup.centralizer (X : Set G) := fun c => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hmemC c x hx).symm
  have finj : Function.Injective f := by
    intro c c' hcc
    have h1 : (c : G)⁻¹ * c' ∈ Subgroup.centralizer (X : Set G) := by
      have := (Subgroup.centralizer (X : Set G)).mul_mem
        ((Subgroup.centralizer (X : Set G)).inv_mem (hcentX c)) (hcentX c')
      rw [hcc] at this
      simpa [mul_assoc] using this
    have h2 : (c : G)⁻¹ * c' ∈ S := S.mul_mem (S.inv_mem (hCS c c.2).1) (hCS c' c'.2).1
    by_contra hne
    have : (c : G)⁻¹ * c' ≠ 1 := fun e => hne (Subtype.ext (by
      have := mul_eq_one_iff_eq_inv.1 e
      simpa using this))
    exact hSc _ h2 this fun x hx => (Subgroup.mem_centralizer_iff.1 h1 x hx).symm
  have hCV : Nat.card ↥C ≤ 4 := by
    have := Nat.card_le_card_of_injective (fun c : ↥C => (⟨f c, hfV c⟩ : ↥(pCoreOf 2 X))) (by
      intro c c' h
      exact finj (congrArg Subtype.val h))
    rw [hb.card] at this
    exact this
  by_cases hall : ∀ s ∈ S, ∀ w ∈ pCoreOf 2 X, s * w = w * s
  · have hSC : S ≤ C := fun s hs =>
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun w hw => (hall s hs w hw).symm, hs⟩
    exact le_trans (Subgroup.card_le_of_le hSC) hCV
  · push Not at hall
    obtain ⟨d, hdS, w₀, hw₀, hdw₀⟩ := hall
    obtain ⟨c₀, hc₀V, hc₀1, hc₀d, hc₀u⟩ :=
      exists_fixed_of_not_centralizes hb hSp hSnV hdS (fun h => hdw₀ (by
        have := h w₀ hw₀
        exact mul_inv_eq_iff_eq_mul.1 this))
    have hfix : ∀ c : ↥C, f c = 1 ∨ f c = c₀ := by
      intro c
      have hdc : d * (c : G) = (c : G) * d := hScomm d hdS c (hCS c c.2).1
      set w := f c with hwdef
      have hwV : w ∈ pCoreOf 2 X := hfV c
      have hw'V : d * w * d⁻¹ ∈ pCoreOf 2 X := conj_mem_pCoreOf (hSn d hdS) hwV
      have h1 : (d * w * d⁻¹) * (c : G) ∈ Subgroup.centralizer (X : Set G) := by
        have e : (d * w * d⁻¹) * (c : G) = d * (w * (c : G)) * d⁻¹ := by
          calc (d * w * d⁻¹) * (c : G) = d * w * (d⁻¹ * (c : G) * d) * d⁻¹ := by group
            _ = d * w * (c : G) * d⁻¹ := by
                have : d⁻¹ * (c : G) * d = (c : G) := by
                  calc d⁻¹ * (c : G) * d = d⁻¹ * (d * (c : G)) := by rw [hdc]; group
                    _ = (c : G) := by group
                rw [this]
            _ = d * (w * (c : G)) * d⁻¹ := by group
        rw [e, Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' : d⁻¹ * x * d ∈ X := by
          have : x ∈ conjSub d X := by rw [hSn d hdS]; exact hx
          exact mem_conjSub_iff.1 this
        have h2 := hmemC c _ hx'
        calc x * (d * (w * (c : G)) * d⁻¹) = d * ((d⁻¹ * x * d) * (w * (c : G))) * d⁻¹ := by group
          _ = d * ((w * (c : G)) * (d⁻¹ * x * d)) * d⁻¹ := by rw [← h2]
          _ = (d * (w * (c : G)) * d⁻¹) * x := by group
      have h3 : (d * w * d⁻¹) * w⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
        have := (Subgroup.centralizer (X : Set G)).mul_mem h1
          ((Subgroup.centralizer (X : Set G)).inv_mem (hcentX c))
        simpa [mul_assoc] using this
      have h4 : (d * w * d⁻¹) * w⁻¹ = 1 :=
        Blk3.eq_one_of_centralizes hb (pCoreOf 2 X |>.mul_mem hw'V ((pCoreOf 2 X).inv_mem hwV))
          (fun x hx => (Subgroup.mem_centralizer_iff.1 h3 x hx).symm)
      have h5 : d * w * d⁻¹ = w := mul_inv_eq_one.1 h4
      exact hc₀u w hwV h5
    have hC2 : Nat.card ↥C ≤ 2 := by
      have hinj : Function.Injective
          (fun c : ↥C => (⟨f c, hfix c⟩ : {x : G // x = 1 ∨ x = c₀})) := by
        intro c c' h
        exact finj (congrArg Subtype.val h)
      have h1 := Nat.card_le_card_of_injective _ hinj
      have h2 : Nat.card {x : G // x = 1 ∨ x = c₀} ≤ 2 := by
        have : {x : G | x = 1 ∨ x = c₀} = {1, c₀} := by ext; simp
        calc Nat.card {x : G // x = 1 ∨ x = c₀} = Nat.card ↥({1, c₀} : Set G) := by
              rw [← this]; rfl
          _ = ({1, c₀} : Set G).ncard := Nat.card_coe_set_eq _
          _ ≤ 2 := by
              refine (Set.ncard_insert_le _ _).trans ?_
              simp
      exact h1.trans h2
    omega

section Bound

variable {M : Subgroup G} {𝒳 : Set (Subgroup G)}

theorem relIndex_normalizer_le [Finite G] (F : Fam M 𝒳) {D : Subgroup G} (hDM : D ≤ M)
    {Y₀ : Subgroup G} (hY₀ : Y₀ ∈ 𝒳) :
    (Subgroup.normalizer (Y₀ : Set G)).relIndex D ≤ Nat.card ↥𝒳 := by
  let N₀ : Subgroup ↥D := (Subgroup.normalizer (Y₀ : Set G)).subgroupOf D
  let f : ↥D ⧸ N₀ → ↥𝒳 := Quotient.lift
    (fun d : ↥D => (⟨conjSub (d : G) Y₀, F.perm d (hDM d.2) Y₀ hY₀⟩ : ↥𝒳)) (by
      intro d d' h
      have h' : d⁻¹ * d' ∈ N₀ := QuotientGroup.leftRel_apply.1 h
      have h1 : ((d⁻¹ * d' : ↥D) : G) ∈ Subgroup.normalizer (Y₀ : Set G) :=
        Subgroup.mem_subgroupOf.1 h'
      have h2 := mem_normalizer_iff_conjSub.1 h1
      apply Subtype.ext
      show conjSub (d : G) Y₀ = conjSub (d' : G) Y₀
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      calc conjSub (d : G) Y₀ = conjSub (d : G) (conjSub ((d : G)⁻¹ * d') Y₀) := by rw [h2]
        _ = conjSub (d' : G) Y₀ := by
            rw [conjSub_conjSub]
            congr 1
            group)
  have hinj : Function.Injective f := by
    intro q q'
    induction q using Quotient.inductionOn with
    | h d =>
    induction q' using Quotient.inductionOn with
    | h d' =>
    intro hf
    have e : conjSub (d : G) Y₀ = conjSub (d' : G) Y₀ := congrArg Subtype.val hf
    refine Quotient.sound (QuotientGroup.leftRel_apply.2 ?_)
    rw [Subgroup.mem_subgroupOf]
    apply mem_normalizer_iff_conjSub.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc conjSub ((d : G)⁻¹ * d') Y₀ = conjSub (d : G)⁻¹ (conjSub d' Y₀) :=
          (conjSub_conjSub _ _ _).symm
      _ = conjSub (d : G)⁻¹ (conjSub d Y₀) := by rw [e]
      _ = Y₀ := conjSub_inv_conjSub _ _
  have := Nat.card_le_card_of_injective f hinj
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact this

theorem lemma6_bound [Finite G] (F : Fam M 𝒳) {D : Subgroup G} (hDM : D ≤ M)
    (hD2 : ∀ x ∈ D, x * x = 1) (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hD : ∀ u ∈ D, u ≠ 1 → ∀ Y ∈ 𝒳, ¬ ∀ x ∈ Y, u * x = x * u) :
    Nat.card D ≤ 4 * Nat.card ↥𝒳 := by
  obtain ⟨Y₀, hY₀, -⟩ := F.two
  obtain ⟨a, ha⟩ := F.blk Y₀ hY₀
  have hS := stab_bound ha (S := Subgroup.normalizer (Y₀ : Set G) ⊓ D)
    (fun s hs => hD2 s (Subgroup.mem_inf.1 hs).2)
    (fun s hs s' hs' => hDc s (Subgroup.mem_inf.1 hs).2 s' (Subgroup.mem_inf.1 hs').2)
    (fun s hs => mem_normalizer_iff_conjSub.1 (Subgroup.mem_inf.1 hs).1)
    (fun s hs hs1 => hD s (Subgroup.mem_inf.1 hs).2 hs1 Y₀ hY₀)
  have h1 := Subgroup.relIndex_mul_card (Subgroup.normalizer (Y₀ : Set G)) D
  have h2 := relIndex_normalizer_le F hDM hY₀
  calc Nat.card D = (Subgroup.normalizer (Y₀ : Set G)).relIndex D *
        Nat.card ↥(Subgroup.normalizer (Y₀ : Set G) ⊓ D) := h1.symm
    _ ≤ Nat.card ↥𝒳 * 4 := Nat.mul_le_mul h2 hS
    _ = 4 * Nat.card ↥𝒳 := by ring

end Bound

theorem card_sup_of_commute {P Q : Subgroup G} (hc : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hinf : ∀ x, x ∈ P → x ∈ Q → x = 1) : Nat.card ↥(P ⊔ Q) = Nat.card P * Nat.card Q := by
  let f : ↥P × ↥Q → ↥(P ⊔ Q) := fun pq =>
    ⟨pq.1.1 * pq.2.1, (mem_sup_of_commute hc).2 ⟨pq.1.1, pq.1.2, pq.2.1, pq.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ e
      have e' : p * q = p' * q' := congrArg Subtype.val e
      have e1 : p'⁻¹ * p = q' * q⁻¹ := by
        calc p'⁻¹ * p = p'⁻¹ * (p * q) * q⁻¹ := by group
          _ = p'⁻¹ * (p' * q') * q⁻¹ := by rw [e']
          _ = q' * q⁻¹ := by group
      have h1 : p'⁻¹ * p = 1 := hinf _ (P.mul_mem (P.inv_mem hp') hp)
        (e1 ▸ Q.mul_mem hq' (Q.inv_mem hq))
      have hpp : p = p' := by
        have := mul_eq_one_iff_eq_inv.1 h1
        simpa using this.symm
      subst hpp
      have h2 : q' * q⁻¹ = 1 := by rw [← e1, h1]
      have hqq : q = q' := by
        have := mul_eq_one_iff_eq_inv.1 h2
        simpa using this.symm
      subst hqq
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_of_commute hc).1 hx
      exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

namespace Fam

variable {M : Subgroup G} {𝒴 : Set (Subgroup G)} (F : Fam M 𝒴)
include F

theorem card_iSup [Finite G] (S : Finset (Subgroup G)) (hS : (S : Set (Subgroup G)) ⊆ 𝒴) :
    Nat.card ↥(⨆ Y ∈ S, pCoreOf 2 Y) = 4 ^ S.card ∧
      (∀ x ∈ (⨆ Y ∈ S, pCoreOf 2 Y), x * x = 1) ∧
      (∀ x ∈ (⨆ Y ∈ S, pCoreOf 2 Y), ∀ y ∈ (⨆ Y ∈ S, pCoreOf 2 Y), x * y = y * x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Finset.card_empty, pow_zero]
    refine ⟨Subgroup.card_bot, ?_, ?_⟩
    · intro x hx
      rw [Subgroup.mem_bot.1 hx, one_mul]
    · intro x hx y hy
      rw [Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy]
  | insert Y S hY ih =>
    have hS' : (S : Set (Subgroup G)) ⊆ 𝒴 := fun Z hZ => hS (by simp [hZ])
    have hY𝒴 : Y ∈ 𝒴 := hS (by simp)
    obtain ⟨ih1, ih2, ih3⟩ := ih hS'
    obtain ⟨a, ha⟩ := F.blk Y hY𝒴
    rw [Finset.iSup_insert, Finset.card_insert_of_notMem hY]
    have hQY : (⨆ Z ∈ S, pCoreOf 2 Z) ≤ Subgroup.centralizer (Y : Set G) := by
      refine iSup₂_le fun Z hZ => ?_
      have hZ𝒴 : Z ∈ 𝒴 := hS' hZ
      have hne : Z ≠ Y := fun e => hY (e ▸ hZ)
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact F.comm Y hY𝒴 Z hZ𝒴 hne.symm y hy z ((pCoreOf_le_self Z) hz)
    have hc : ∀ p ∈ pCoreOf 2 Y, ∀ q ∈ (⨆ Z ∈ S, pCoreOf 2 Z), p * q = q * p := by
      intro p hp q hq
      have := Subgroup.mem_centralizer_iff.1 (hQY hq) p ((pCoreOf_le_self Y) hp)
      exact this
    have hinf : ∀ x, x ∈ pCoreOf 2 Y → x ∈ (⨆ Z ∈ S, pCoreOf 2 Z) → x = 1 := by
      intro x hx hxQ
      refine Blk3.eq_one_of_centralizes ha hx fun y hy => ?_
      exact (Subgroup.mem_centralizer_iff.1 (hQY hxQ) y hy).symm
    refine ⟨?_, ?_, ?_⟩
    · rw [card_sup_of_commute hc hinf, ih1, ha.card]
      ring
    · intro x hx
      obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_of_commute hc).1 hx
      have c1 := hc p hp q hq
      calc p * q * (p * q) = p * (q * p) * q := by group
        _ = p * (p * q) * q := by rw [← c1]
        _ = (p * p) * (q * q) := by group
        _ = 1 := by rw [ha.sq p hp, ih2 q hq, one_mul]
    · intro x hx x' hx'
      obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_of_commute hc).1 hx
      obtain ⟨p', hp', q', hq', rfl⟩ := (mem_sup_of_commute hc).1 hx'
      have c1 := ha.comm _ hp _ hp'
      have c2 := ih3 q hq q' hq'
      have c3 := hc p hp q' hq'
      have c4 := hc p' hp' q hq
      calc p * q * (p' * q') = p * (q * p') * q' := by group
        _ = p * (p' * q) * q' := by rw [← c4]
        _ = (p * p') * (q * q') := by group
        _ = (p' * p) * (q' * q) := by rw [c1, c2]
        _ = p' * (p * q') * q := by group
        _ = p' * (q' * p) * q := by rw [c3]
        _ = p' * q' * (p * q) := by group

end Fam


theorem pow_gt_aux {r : ℕ} (hr : 3 ≤ r) : 4 * r < 4 ^ (r - 1) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 1 ≤ 4 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 4 ^ (n + 1 - 1) = 4 * 4 ^ (n - 1) := by
      have : n + 1 - 1 = (n - 1) + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [h2]
    omega

namespace Fam

variable {M : Subgroup G} {𝒳 : Set (Subgroup G)} (F : Fam M 𝒳)
include F

theorem not_le_conj {g : G} (hg : g ∉ M) : ∀ Y ∈ 𝒳, ¬ Y ≤ conjSub g M := by
  intro Y hY hle
  apply hg
  have h1 := conjSub_mono (g := g⁻¹) hle
  rw [conjSub_inv_conjSub] at h1
  have := F.conj_le Y hY g⁻¹ h1
  simpa using M.inv_mem this

theorem lemma6 [Finite G] (hr : 3 ≤ Nat.card ↥𝒳) {g : G} (hg : g ∉ M)
    (hW : ∀ Y ∈ 𝒳, pCoreOf 2 (conjSub g Y) ≤ M) : False := by
  classical
  have F' := F.conj g
  have hX : ∀ Y ∈ 𝒳, ¬ Y ≤ conjSub g M := F.not_le_conj hg
  obtain ⟨Y₀, hY₀, -⟩ := F'.two
  have hfin : (conjSub g '' 𝒳).Finite := Set.toFinite _
  let 𝒴f : Finset (Subgroup G) := hfin.toFinset
  have hmem : ∀ Y, Y ∈ 𝒴f ↔ Y ∈ conjSub g '' 𝒳 := fun Y => Set.Finite.mem_toFinset hfin
  let S : Finset (Subgroup G) := 𝒴f.erase Y₀
  have hSsub : (S : Set (Subgroup G)) ⊆ conjSub g '' 𝒳 := by
    intro Y hY
    exact (hmem Y).1 (Finset.mem_of_mem_erase hY)
  have hcard𝒴 : 𝒴f.card = Nat.card ↥𝒳 := by
    have h1 : (conjSub g '' 𝒳).ncard = 𝒳.ncard :=
      Set.ncard_image_of_injective _ (conjSub_injective g)
    rw [Set.ncard_eq_toFinset_card _ hfin] at h1
    rw [h1, Nat.card_coe_set_eq]
  have hY₀f : Y₀ ∈ 𝒴f := (hmem Y₀).2 hY₀
  have hScard : S.card = Nat.card ↥𝒳 - 1 := by
    rw [Finset.card_erase_of_mem hY₀f, hcard𝒴]
  obtain ⟨hcardD, hsqD, hcommD⟩ := F'.card_iSup S hSsub
  have hDM : (⨆ Y ∈ S, pCoreOf 2 Y) ≤ M := iSup₂_le fun Y hY => by
    obtain ⟨Y', hY', rfl⟩ := hSsub (Finset.mem_coe.2 hY)
    exact hW Y' hY'
  have hcentY₀ : (⨆ Y ∈ S, pCoreOf 2 Y) ≤ Subgroup.centralizer (Y₀ : Set G) :=
    iSup₂_le fun Y hY => by
      have hne : Y ≠ Y₀ := (Finset.mem_erase.1 hY).1
      have hY𝒴 : Y ∈ conjSub g '' 𝒳 := hSsub (Finset.mem_coe.2 hY)
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact F'.comm Y₀ hY₀ Y hY𝒴 hne.symm y hy z ((pCoreOf_le_self Y) hz)
  have hspade : ∀ u ∈ (⨆ Y ∈ S, pCoreOf 2 Y), u ≠ 1 → ∀ Y ∈ 𝒳, ¬ ∀ x ∈ Y, u * x = x * u := by
    intro u hu hu1 Y hY hcY
    have hN : Subgroup.centralizer ({u} : Set G) ≤ conjSub g M :=
      F'.cent u hu1 (hsqD u hu) ⟨Y₀, hY₀, fun x hx =>
        (Subgroup.mem_centralizer_iff.1 (hcentY₀ hu) x hx).symm⟩
    apply hX Y hY
    intro x hx
    apply hN
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcY x hx).symm
  have hb := lemma6_bound F hDM hsqD hcommD hspade
  rw [hcardD, hScard] at hb
  have := pow_gt_aux hr
  omega

theorem lemma34_big [Finite G] (hr : 3 ≤ Nat.card ↥𝒳) {U : Subgroup G} (hUM : U ≤ M)
    (hU : IsKleinFour ↥U) {g : G}
    (hC : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ conjSub g M) : g ∈ M := by
  by_contra hg
  exact F.lemma6 hr hg (cor1star F hg hUM hU hC).2

end Fam

end CFSG.CGT.PushingUpLit.A4.L34

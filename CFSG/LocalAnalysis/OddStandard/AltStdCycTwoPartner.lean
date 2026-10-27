module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSwap
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartNear

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

section Transport

omit [Finite G] in
theorem z_mem_centralizer_corr_of_le (hLz : L ≤ centralizer ({z} : Set G))
    (θ : L ≃* alternatingGroup (Fin n)) (T' : Subgroup (Perm (Fin n))) :
    z ∈ centralizer (corr (X := G) θ T' : Set G) := by
  rw [mem_centralizer_iff]
  intro r hr
  exact mem_centralizer_singleton_iff.1 (hLz (corr_le θ T' hr))

theorem exists_secEquiv_of_card_eq_of_le (hLz : L ≤ centralizer ({z} : Set G))
    (θ : L ≃* alternatingGroup (Fin n)) {S S' : Finset (Fin n)} (hS : S.card = S'.card)
    (hSc : 2 ≤ Sᶜ.card) :
    ∃ (ht : z ∈ centralizer (corr (X := G) θ (altSub S) : Set G))
      (ht' : z ∈ centralizer (corr (X := G) θ (altSub S') : Set G))
      (Φ : Sec G (corr (X := G) θ (altSub S)) ≃* Sec G (corr (X := G) θ (altSub S'))),
      Φ (QuotientGroup.mk ⟨z, ht⟩) = QuotientGroup.mk ⟨z, ht'⟩ := by
  have ht := z_mem_centralizer_corr_of_le hLz θ (altSub S)
  have ht' := z_mem_centralizer_corr_of_le hLz θ (altSub S')
  obtain ⟨π, hsign, hπ⟩ := exists_even_perm_of_card_eq hS hSc
  have hπA : π ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 hsign
  have hlgL : ((θ.symm ⟨π, hπA⟩ : L) : G) ∈ L := (θ.symm ⟨π, hπA⟩ : L).2
  have hlz : ((θ.symm ⟨π, hπA⟩ : L) : G) * z * ((θ.symm ⟨π, hπA⟩ : L) : G)⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 (hLz hlgL)]
    group
  have hRS := corr_conj_iff (G := G) θ hπA hπ
  refine ⟨ht, ht', secConj _ hRS, ?_⟩
  rw [secConj_mk]
  congr 1
  exact Subtype.ext hlz

theorem caseIAt_transport_of_le (hLz : L ≤ centralizer ({z} : Set G))
    (θ : L ≃* alternatingGroup (Fin n)) {S S' : Finset (Fin n)} (hS : S.card = S'.card)
    (hSc : 2 ≤ Sᶜ.card) (hI : CaseIAt θ z S) : CaseIAt θ z S' := by
  obtain ⟨ht0, hc⟩ := hI
  obtain ⟨ht, ht', Φ, hΦ⟩ := exists_secEquiv_of_card_eq_of_le hLz θ hS hSc
  refine ⟨ht', ?_⟩
  rw [← hΦ, Subgroup.mem_center_iff]
  intro y
  obtain ⟨y', rfl⟩ := Φ.surjective y
  have hc' := Subgroup.mem_center_iff.1 hc y'
  rw [← map_mul, ← map_mul, hc']

theorem caseIIAt_transport_of_le (hLz : L ≤ centralizer ({z} : Set G))
    (θ : L ≃* alternatingGroup (Fin n)) {S S' : Finset (Fin n)} (hS : S.card = S'.card)
    (hSc : 2 ≤ Sᶜ.card) (hII : CaseIIAt θ z S) : CaseIIAt θ z S' := by
  obtain ⟨ht0, hs⟩ := hII
  obtain ⟨ht, ht', Φ, hΦ⟩ := exists_secEquiv_of_card_eq_of_le hLz θ hS hSc
  refine ⟨ht', ?_⟩
  have := SymOutcome.map' Φ hs
  rw [hΦ] at this
  rw [← hS]
  exact this

end Transport

section Root

theorem oddY_le_centralizer_corr (d : Cyc L Q z) (θ : L ≃* alternatingGroup (Fin n))
    (T' : Subgroup (Perm (Fin n))) :
    oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ≤
      centralizer (corr (X := G) θ T' : Set G) := by
  intro y hy
  rw [mem_centralizer_iff]
  intro r hr
  exact mem_centralizer_iff.1 (oddY_le_centralizer d hy) r (corr_le θ T' hr)

theorem orderOf_permOf_conj (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n)) {a g : G}
    (hg : g * z * g⁻¹ = a) (haz : a ≠ z) (ha' : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) :
    orderOf (permOf B θ ha') = 2 := by
  have hz2 : z * z = 1 := B.cyc.mul_self
  have hz1 : z ≠ 1 := fun h1 => by simpa [h1] using B.cyc.order
  have ha'2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  have hsq : permOf B θ ha' * permOf B θ ha' = 1 := by
    rw [← permOf_mul B θ ha' ha' (mul_mem ha' ha'),
      permOf_congr B θ ha'2 (mul_mem ha' ha') (one_mem _), permOf_one]
  have hne : permOf B θ ha' ≠ 1 := by
    intro h1
    have hc := (permOf_eq_one_iff B θ ha').1 h1
    have hzp : g⁻¹ * z * g ∈ zpowers z :=
      mem_zpowers_of_two_pow B.cyc B.card ⟨hc, ha'⟩ (k := 1) (by rw [pow_one, pow_two]; exact ha'2)
    have hQ : g⁻¹ * z * g ∈ Q := by
      rw [eq_zpowers_of_card_eq_two_of_cyc B.cyc B.card]; exact hzp
    rcases eq_one_or_eq_of_card_eq_two B.cyc B.card hQ with h2 | h2
    · apply hz1
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h2]; group
    · apply haz
      rw [← hg]
      calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h2]
        _ = z := by group
  have hdvd : orderOf (permOf B θ ha') ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.1 h1) hne
  · exact h2

theorem exists_corr_eq_conj₂ (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {a g : G} (ha : a ∈ centralizer ({z} : Set G)) (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf5 : 5 ≤ (fixFin (permOf T.toBase θ ha)).card) :
    ∃ F' : Finset (Fin n), F'.card = (fixFin (permOf T.toBase θ ha)).card ∧
      conjSub g⁻¹ (corr (X := G) θ (altSub (fixFin (permOf T.toBase θ ha)))) =
        corr (X := G) θ (altSub F') := by
  set F : Finset (Fin n) := fixFin (permOf T.toBase θ ha) with hF
  set N : Subgroup G := corr (X := G) θ (altSub F) with hN
  have ha' : g⁻¹ * z * g ∈ centralizer ({z} : Set G) := conj_inv_mem_centralizer ha hg
  have hz2 : z * z = 1 := T.cyc.mul_self
  have ha'2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  have hNL : N ≤ L := corr_le θ _
  have hNa : ∀ w ∈ N, a * w = w * a := fun w hw =>
    comm_of_mem_corr_of_permOf_fix T.toBase θ ha (fun i hi => mem_fixFin.1 hi) hw
  have hNz : ∀ w ∈ N, w * z = z * w := fun w hw =>
    mem_centralizer_singleton_iff.1 (le_cent_single T.std T.cyc (hNL hw))
  have hKz : ∀ w ∈ N, (g⁻¹ * w * g) ∈ centralizer ({z} : Set G) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    have h1 := hNa w hw
    rw [← hg] at h1
    calc g⁻¹ * w * g * z = g⁻¹ * (w * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * w) * g := by rw [h1]
      _ = z * (g⁻¹ * w * g) := by group
  have hKC : ∀ x ∈ conjSub g⁻¹ N, x ∈ centralizer ({z} : Set G) := by
    intro x hx
    have hw := mem_conjSub_inv_iff.1 hx
    have := hKz _ hw
    simpa [mul_assoc] using this
  obtain ⟨φ⟩ := exists_equiv_corr_altSub (X := G) θ F
  let ψ : ↥N ≃* ↥(conjSub g⁻¹ N) :=
    N.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hφ' : ↥(conjSub g⁻¹ N) ≃* alternatingGroup (Fin F.card) := ψ.symm.trans φ
  have hKLY : conjSub g⁻¹ N ≤
      L ⊔ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) :=
    le_of_forall_orderOf_three hφ' fun x hx hx3 =>
      mem_sup_oddY_of_odd T (hKC x hx) (by rw [hx3]; exact ⟨1, rfl⟩)
  obtain ⟨θ'⟩ := T.iso
  have hYN : oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ≤
      normalizer (L : Set G) :=
    (oddY_le_centralizer T.cyc).trans (Subgroup.centralizer_le_normalizer _)
  have hsetLY := Subgroup.coe_mul_of_right_le_normalizer_left L _ hYN
  have hinvL : ∀ x ∈ conjSub g⁻¹ N, x * x = 1 → x ∈ L := by
    intro x hx hx2
    have hx' : x ∈ (L : Set G) *
        (oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) : Set G) := by
      rw [← hsetLY]
      exact hKLY hx
    obtain ⟨l, hl, y, hy, rfl⟩ := Set.mem_mul.1 hx'
    have hyK := oddY_le_centralizer T.cyc hy
    have hly : l * y = y * l := mem_centralizer_iff.1 hyK l hl
    have h1 : (l * l) * (y * y) = 1 := by
      calc (l * l) * (y * y) = l * (l * y) * y := by group
        _ = l * (y * l) * y := by rw [hly]
        _ = (l * y) * (l * y) := by group
        _ = 1 := hx2
    have hllK : l * l ∈ centralizer (L : Set G) := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (mul_mem hyK hyK)
    have hll : l * l = 1 :=
      eq_one_of_mem_of_mem_centralizer θ' (by have := T.hn; omega) (mul_mem hl hl) hllK
    have hyy : y * y = 1 := by rw [hll, one_mul] at h1; exact h1
    have hy1 : y = 1 := by
      have hodd := odd_orderOf_of_mem_oddY T.cyc hy
      have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hyy)
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact orderOf_eq_one_iff.1 h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    rw [hy1, mul_one]
    exact hl
  have hN'L : conjSub g⁻¹ N ≤ L := by
    have : IsSimpleGroup (alternatingGroup (Fin F.card)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have hsimple : IsSimpleGroup ↥(conjSub g⁻¹ N) := hφ'.isSimpleGroup
    have hHn : (L.subgroupOf (conjSub g⁻¹ N)).Normal := by
      refine ⟨fun b hb c => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hb ⊢
      have hcN : (c : G) ∈ normalizer (L : Set G) := cent_le_normalizer T.std T.cyc (hKC _ c.2)
      simpa using (mem_normalizer_iff.1 hcN _).1 hb
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf (conjSub g⁻¹ N)) with
      hbot | htop
    · exfalso
      have h2K : 2 ∣ Nat.card ↥(conjSub g⁻¹ N) := by
        rw [card_eq_of_equiv_alt (by omega) hφ']
        have h4 : 4 ∣ F.card.factorial := Nat.dvd_factorial (by norm_num) (by omega)
        omega
      obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(conjSub g⁻¹ N)) 2 h2K
      have hxx : (x : G) * (x : G) = 1 := by
        have h1 := pow_orderOf_eq_one x
        rw [hx2, pow_two] at h1
        exact congrArg Subtype.val h1
      have hxL : x ∈ L.subgroupOf (conjSub g⁻¹ N) := hinvL _ x.2 hxx
      rw [hbot] at hxL
      have hx1 : x = 1 := hxL
      rw [hx1, orderOf_one] at hx2
      omega
    · intro x hx
      have : (⟨x, hx⟩ : ↥(conjSub g⁻¹ N)) ∈ L.subgroupOf (conjSub g⁻¹ N) := by
        rw [htop]
        trivial
      exact this
  set ye' : Perm (Fin n) := permOf T.toBase θ ha' with hye'
  have hye'2 : orderOf ye' = 2 := orderOf_permOf_conj T.toBase θ hg haz ha'
  have hKt : permImg θ (conjSub g⁻¹ N) ≤ centralizer ({ye'} : Set (Perm (Fin n))) := by
    intro σ hσ
    obtain ⟨x, hx, rfl⟩ := (mem_permImg θ).1 hσ
    rw [mem_centralizer_singleton_iff]
    obtain ⟨w, hw, hwx⟩ : ∃ w ∈ N, g⁻¹ * w * g = (x : G) :=
      ⟨g * x * g⁻¹, mem_conjSub_inv_iff.1 hx, by group⟩
    have hxc : (x : G) * (g⁻¹ * z * g) = (g⁻¹ * z * g) * x := by
      rw [← hwx]
      calc g⁻¹ * w * g * (g⁻¹ * z * g) = g⁻¹ * (w * z) * g := by group
        _ = g⁻¹ * (z * w) * g := by rw [hNz w hw]
        _ = (g⁻¹ * z * g) * (g⁻¹ * w * g) := by group
    have hxC : (x : G) ∈ centralizer ({z} : Set G) := le_cent_single T.std T.cyc x.2
    have h1 := permOf_of_mem T.toBase θ hxC x.2
    have h2 : permOf T.toBase θ hxC * permOf T.toBase θ ha' =
        permOf T.toBase θ ha' * permOf T.toBase θ hxC := by
      rw [← permOf_mul T.toBase θ hxC ha' (mul_mem hxC ha'),
        ← permOf_mul T.toBase θ ha' hxC (mul_mem ha' hxC)]
      exact permOf_congr T.toBase θ hxc _ _
    have h3 : ((θ x : alternatingGroup (Fin n)) : Perm (Fin n)) * ye' =
        ye' * ((θ x : alternatingGroup (Fin n)) : Perm (Fin n)) := by
      rw [← h1]
      exact h2
    exact h3
  have hKn : ∀ c ∈ centralizer ({ye'} : Set (Perm (Fin n))),
      ∀ k ∈ permImg θ (conjSub g⁻¹ N), c * k * c⁻¹ ∈ permImg θ (conjSub g⁻¹ N) := by
    intro c hc k hk
    have hc' : c * ye' = ye' * c := mem_centralizer_singleton_iff.1 hc
    obtain ⟨s, hsC, hs, hsa'⟩ := exists_lift_commuting T θ ha' ha'2 hc'
    obtain ⟨x, hx, rfl⟩ := (mem_permImg θ).1 hk
    obtain ⟨w, hw, hwx⟩ : ∃ w ∈ N, g⁻¹ * w * g = (x : G) :=
      ⟨g * x * g⁻¹, mem_conjSub_inv_iff.1 hx, by group⟩
    have hyz : g * s * g⁻¹ * z = z * (g * s * g⁻¹) := by
      have h1 : s * (g⁻¹ * z * g) = (g⁻¹ * z * g) * s := hsa'
      calc g * s * g⁻¹ * z = g * (s * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * s) * g⁻¹ := by rw [h1]
        _ = z * (g * s * g⁻¹) := by group
    have hyC : g * s * g⁻¹ ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hyz
    have hya : g * s * g⁻¹ * a = a * (g * s * g⁻¹) := by
      have h1 := mem_centralizer_singleton_iff.1 hsC
      rw [← hg]
      calc g * s * g⁻¹ * (g * z * g⁻¹) = g * (s * z) * g⁻¹ := by group
        _ = g * (z * s) * g⁻¹ := by rw [h1]
        _ = (g * z * g⁻¹) * (g * s * g⁻¹) := by group
    have hynorm := mem_normalizer_corr_fixFin T.toBase θ ha hyC hya
    have hywy : (g * s * g⁻¹) * w * (g * s * g⁻¹)⁻¹ ∈ N := (mem_normalizer_iff.1 hynorm w).1 hw
    have hsx : s * (x : G) * s⁻¹ = g⁻¹ * ((g * s * g⁻¹) * w * (g * s * g⁻¹)⁻¹) * g := by
      rw [← hwx]
      group
    have hsxL : s * (x : G) * s⁻¹ ∈ L := by
      rw [hsx]
      exact hN'L (mem_conjSub_inv_iff.2 (by simpa [mul_assoc] using hywy))
    refine (mem_permImg θ).2 ⟨⟨s * (x : G) * s⁻¹, hsxL⟩, ?_, ?_⟩
    · show s * (x : G) * s⁻¹ ∈ conjSub g⁻¹ N
      exact mem_conjSub_inv_iff.2 (by rw [hsx]; simpa [mul_assoc] using hywy)
    · have hsN : s ∈ normalizer (L : Set G) := cent_le_normalizer T.std T.cyc hsC
      have h1 := rho_conj_apply θ T.hn hsN x ⟨s * (x : G) * s⁻¹, hsxL⟩ rfl
      have h2 : rho θ T.hn ⟨s, hsN⟩ = c := hs
      rw [h2] at h1
      rw [← h1]
  have hKequiv : Nonempty (permImg θ (conjSub g⁻¹ N) ≃* alternatingGroup (Fin F.card)) :=
    ⟨((permImgEquiv θ hN'L).symm.trans ψ.symm).trans φ⟩
  obtain ⟨hKeq, hcard⟩ := normalAltIdentSym_of_five_le hf5 ye' hye'2 _ (permImg_le_alt θ _) hKt
    hKn hKequiv
  refine ⟨fixFin ye', hcard, ?_⟩
  rw [← hKeq]
  exact (corr_permImg θ hN'L).symm

theorem exists_common_root₂ (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {a g : G} (ha : a ∈ centralizer ({z} : Set G)) (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf T.toBase θ ha)).card ∧ (fixFin (permOf T.toBase θ ha)).card ≠ 6)
    {S : Finset (Fin n)} (hS : S ⊆ fixFin (permOf T.toBase θ ha)) :
    ∃ S₁ : Finset (Fin n), S₁.card = S.card ∧
      rootGroup (G := G) θ S = conjSub g (rootGroup θ S₁) := by
  set F : Finset (Fin n) := fixFin (permOf T.toBase θ ha) with hF
  obtain ⟨F', hcard, hconj⟩ := exists_corr_eq_conj₂ T θ ha hg haz hf.1
  have hFF' : ∀ x ∈ corr (X := G) θ (altSub F), g⁻¹ * x * g ∈ corr (X := G) θ (altSub F') := by
    intro x hx
    rw [← hconj]
    refine mem_conjSub_iff.2 ?_
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    simpa [this] using hx
  have hF'F : ∀ x ∈ corr (X := G) θ (altSub F'), g * x * g⁻¹ ∈ corr (X := G) θ (altSub F) := by
    intro x hx
    rw [← hconj] at hx
    simpa using mem_conjSub_iff.1 hx
  obtain ⟨β, hβ1, hβ2, hβ3, hβ4⟩ :=
    exists_conj_intertwining θ g hcard.symm (Or.inl hf) hFF' hF'F
  refine ⟨S.image β, ?_, rootGroup_eq_conjSub_image θ g hFF' hF'F hβ1 hβ2 hβ3 hβ4 hS⟩
  exact Finset.card_image_of_injOn fun i hi j hj hij => hβ2 i (hS hi) j (hS hj) hij

theorem exists_partner_root_at (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {a g : G} (ha : a ∈ centralizer ({z} : Set G)) (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf T.toBase θ ha)).card ∧ (fixFin (permOf T.toBase θ ha)).card ≠ 6)
    {S : Finset (Fin n)} (hSF : S ⊆ fixFin (permOf T.toBase θ ha)) :
    ∃ S₁ : Finset (Fin n), S₁.card = S.card ∧
      ∃ (hz₁ : z ∈ centralizer (corr (X := G) θ (altSub S₁) : Set G))
        (haR : a ∈ centralizer (corr (X := G) θ (altSub S) : Set G))
        (Φ : Sec G (corr (X := G) θ (altSub S₁)) ≃* Sec G (corr (X := G) θ (altSub S))),
        Φ (QuotientGroup.mk ⟨z, hz₁⟩) = QuotientGroup.mk ⟨a, haR⟩ := by
  obtain ⟨S₁, hS₁card, hrS⟩ := exists_common_root₂ T θ ha hg haz hf hSF
  have hz₁ := z_mem_centralizer_corr_of_le (le_cent_single T.std T.cyc) θ (altSub S₁)
  have haR : a ∈ centralizer (corr (X := G) θ (altSub S) : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (comm_of_mem_corr_of_permOf_fix T.toBase θ ha (fun i hi => mem_fixFin.1 (hSF hi))
      hw).symm
  obtain ⟨Φ, hΦ⟩ := exists_secEquiv_of_conj θ hrS hg hz₁ haR
  exact ⟨S₁, hS₁card, hz₁, haR, Φ, hΦ⟩

theorem exists_partner_root (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) {k : ℕ}
    (hk : k ≤ 4) {a g : G} (ha : a ∈ centralizer ({z} : Set G)) (hg : g * z * g⁻¹ = a)
    (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf T.toBase θ ha)).card ∧ (fixFin (permOf T.toBase θ ha)).card ≠ 6) :
    ∃ S S₁ : Finset (Fin n), S ⊆ fixFin (permOf T.toBase θ ha) ∧ S.card = k ∧ S₁.card = k ∧
      ∃ (hz₁ : z ∈ centralizer (corr (X := G) θ (altSub S₁) : Set G))
        (haR : a ∈ centralizer (corr (X := G) θ (altSub S) : Set G))
        (Φ : Sec G (corr (X := G) θ (altSub S₁)) ≃* Sec G (corr (X := G) θ (altSub S))),
        Φ (QuotientGroup.mk ⟨z, hz₁⟩) = QuotientGroup.mk ⟨a, haR⟩ := by
  classical
  obtain ⟨S, hSF, hScard⟩ :=
    Finset.exists_subset_card_eq (show k ≤ (fixFin (permOf T.toBase θ ha)).card by omega)
  obtain ⟨S₁, hS₁card, hz₁, haR, Φ, hΦ⟩ := exists_partner_root_at T θ ha hg haz hf hSF
  exact ⟨S, S₁, hSF, hScard, hS₁card.trans hScard, hz₁, haR, Φ, hΦ⟩

end Root

section Near

theorem mk_eq_conj_thetaHom_or (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} {a : G} (ha : a ∈ centralizer ({z} : Set G)) (haa : a * a = 1)
    {σ : Perm ↥Sᶜ} (hσ : Perm.ofSubtype σ = permOf T.toBase θ ha)
    (haR : a ∈ centralizer (corr (X := G) θ (altSub S) : Set G))
    (hzS : z ∈ centralizer (corr (X := G) θ (altSub S) : Set G)) :
    ∃ y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)),
      ∃ hyR : y ∈ centralizer (corr (X := G) θ (altSub S) : Set G),
        (QuotientGroup.mk ⟨a, haR⟩ : Sec G (corr (X := G) θ (altSub S))) =
            QuotientGroup.mk ⟨y, hyR⟩ * thetaHom T θ S σ * (QuotientGroup.mk ⟨y, hyR⟩)⁻¹ ∨
          (QuotientGroup.mk ⟨a, haR⟩ : Sec G (corr (X := G) θ (altSub S))) =
            QuotientGroup.mk ⟨y, hyR⟩ * (QuotientGroup.mk ⟨z, hzS⟩ * thetaHom T θ S σ) *
              (QuotientGroup.mk ⟨y, hyR⟩)⁻¹ := by
  have hκ : kappa T θ S σ = (swapIota T θ (permOf T.toBase θ ha) : G) := by
    rw [kappa_apply, hσ]
  obtain ⟨y, hy, h⟩ := exists_oddY_conj_swapIota T θ ha haa
  have hyR := oddY_le_centralizer_corr T.cyc θ (altSub S) hy
  refine ⟨y, hy, hyR, ?_⟩
  rw [thetaHom_apply]
  rcases h with h1 | h1
  · left
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hκ]
    exact h1
  · right
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hκ]
    exact h1

private theorem isSwap_conj {α : Type*} [DecidableEq α] {τ : Perm α} (hτ : τ.IsSwap)
    (c : Perm α) : (c * τ * c⁻¹).IsSwap := by
  obtain ⟨x, y, hxy, rfl⟩ := hτ
  exact ⟨c x, c y, fun h => hxy (c.injective h), (Equiv.swap_apply_apply c x y).symm⟩

private theorem mk_z_mul_self (B : Base G L Q n z) {R : Subgroup G}
    (hz : z ∈ centralizer (R : Set G)) :
    (QuotientGroup.mk ⟨z, hz⟩ : Sec G R) * QuotientGroup.mk ⟨z, hz⟩ = 1 := by
  rw [← QuotientGroup.mk_mul]
  have : (⟨z, hz⟩ : ↥(centralizer (R : Set G))) * ⟨z, hz⟩ = 1 := Subtype.ext B.cyc.mul_self
  rw [this]
  rfl

theorem near_partner_swap (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hII : CaseIIAt θ z S₀) {a g : G} (ha : a ∈ centralizer ({z} : Set G))
    (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf T.toBase θ ha)).card ∧ (fixFin (permOf T.toBase θ ha)).card ≠ 6) :
    (permOf T.toBase θ ha).IsSwap := by
  classical
  obtain ⟨S, S₁, hSF, hScard, hS₁card, hz₁, haR, Φ, hΦ⟩ :=
    exists_partner_root T θ (show S₀.card ≤ 4 by omega) ha hg haz hf
  have hLz := le_cent_single T.std T.cyc
  have hSc : 2 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  obtain ⟨hz₁', hs₁⟩ := caseIIAt_transport_of_le hLz θ (show S₀.card = S₁.card by omega) hSc hII
  obtain ⟨hzS, ε, hε⟩ := caseIIAt_transport_of_le hLz θ (show S₀.card = S.card by omega) hSc hII
  have hsa : SymOutcome (QuotientGroup.mk ⟨a, haR⟩ : Sec G (corr (X := G) θ (altSub S)))
      (n - S.card) := by
    have := SymOutcome.map' Φ hs₁
    rw [hΦ, hS₁card, ← hScard] at this
    exact this
  obtain ⟨ε', hε'⟩ := hsa
  set zb : Sec G (corr (X := G) θ (altSub S)) := QuotientGroup.mk ⟨z, hzS⟩ with hzb
  set ab : Sec G (corr (X := G) θ (altSub S)) := QuotientGroup.mk ⟨a, haR⟩ with hab
  have hSc5 : 5 ≤ Sᶜ.card := by rw [card_compl_fin]; omega
  have hScn : Sᶜ.card = n - S.card := card_compl_fin S
  have hτ' : (ε.symm ab).IsSwap := by
    have := isSwap_map_of_mulEquiv (ε'.trans ε.symm) rfl (by simp only [Fintype.card_fin]; omega)
      hε'
    simpa using this
  have hz2 : z * z = 1 := T.cyc.mul_self
  have haa : a * a = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hza : ab * zb = zb * ab := by
    rw [hab, hzb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 ha)
  have hne : ab ≠ zb := mk_ne_of_partner T.cyc ha haz haa hzS haR
  have hzz : zb * zb = 1 := mk_z_mul_self T.toBase hzS
  obtain ⟨σ, hσf⟩ := exists_ofSubtype_eq (fun i hi => mem_fixFin.1 (hSF hi))
  obtain ⟨y, hy, hyR, hyab⟩ := mk_eq_conj_thetaHom_or T θ ha haa hσf haR hzS
  rw [← hab, ← hzb] at hyab
  set yb : Sec G (corr (X := G) θ (altSub S)) := QuotientGroup.mk ⟨y, hyR⟩ with hyb
  have hyz : yb * zb = zb * yb := by
    rw [hyb, hzb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (oddY_le_centralizer_z T.cyc hy))
  set ab' : Sec G (corr (X := G) θ (altSub S)) := yb⁻¹ * ab * yb with hab'
  have hab'cases : ab' = thetaHom T θ S σ ∨ ab' = zb * thetaHom T θ S σ := by
    rcases hyab with h | h
    · left
      rw [hab', h]
      group
    · right
      rw [hab', h]
      group
  have hyz' : yb⁻¹ * zb = zb * yb⁻¹ := by
    calc yb⁻¹ * zb = yb⁻¹ * (zb * yb) * yb⁻¹ := by group
      _ = yb⁻¹ * (yb * zb) * yb⁻¹ := by rw [hyz]
      _ = zb * yb⁻¹ := by group
  have hab'z : ab' * zb = zb * ab' := by
    calc ab' * zb = yb⁻¹ * ab * (yb * zb) := by rw [hab']; group
      _ = yb⁻¹ * ab * (zb * yb) := by rw [hyz]
      _ = yb⁻¹ * (ab * zb) * yb := by group
      _ = yb⁻¹ * (zb * ab) * yb := by rw [hza]
      _ = (yb⁻¹ * zb) * ab * yb := by group
      _ = (zb * yb⁻¹) * ab * yb := by rw [hyz']
      _ = zb * ab' := by rw [hab']; group
  have hab'ne : ab' ≠ zb := by
    intro h
    apply hne
    calc ab = yb * ab' * yb⁻¹ := by rw [hab']; group
      _ = yb * zb * yb⁻¹ := by rw [h]
      _ = zb := by rw [hyz]; group
  have hτ'' : (ε.symm ab').IsSwap := by
    have h1 : ε.symm ab' = (ε.symm yb)⁻¹ * ε.symm ab * ((ε.symm yb)⁻¹)⁻¹ := by
      rw [hab', map_mul, map_mul, map_inv, inv_inv]
    rw [h1]
    exact isSwap_conj hτ' _
  set Ψ : Perm ↥Sᶜ →* Perm (Fin (n - S.card + 2)) :=
    ε.symm.toMonoidHom.comp (thetaHom T θ S) with hΨ
  have hinj : Function.Injective Ψ :=
    ε.symm.injective.comp (thetaHom_injective T θ hSc5)
  have hcomm : ∀ π, Ψ π * ε.symm zb = ε.symm zb * Ψ π := by
    intro π
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, thetaHom_comm_z T θ S hzS π]
  have hneΨ : ∀ π, Ψ π ≠ ε.symm zb := by
    intro π hπ
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hπ
    exact thetaHom_ne_z T θ S hzS π (ε.symm.injective hπ)
  have hτ'c : ε.symm ab' * ε.symm zb = ε.symm zb * ε.symm ab' := by
    rw [← map_mul, ← map_mul, hab'z]
  have hτ'ne : ε.symm ab' ≠ ε.symm zb := fun h' => hab'ne (ε.symm.injective h')
  have hσΨ : Ψ σ = ε.symm ab' ∨ Ψ σ = ε.symm zb * ε.symm ab' := by
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rcases hab'cases with h1 | h1
    · left
      rw [h1]
    · right
      rw [← map_mul, h1, ← mul_assoc, hzz, one_mul]
  have hσswap : σ.IsSwap := by
    refine isSwap_of_embedding (α := ↥Sᶜ) (β := Fin (n - S.card + 2)) ?_ ?_ Ψ hinj hε hcomm
      hneΨ hτ'' hτ'c hτ'ne hσΨ
    · simp only [Fintype.card_fin, Fintype.card_coe]; omega
    · simp only [Fintype.card_coe]; omega
  have := hσswap.of_subtype_isSwap
  rwa [hσf] at this

theorem near_partner_false (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hI : CaseIAt θ z S₀) {a g : G} (ha : a ∈ centralizer ({z} : Set G))
    (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf T.toBase θ ha)).card ∧ (fixFin (permOf T.toBase θ ha)).card ≠ 6) :
    False := by
  classical
  obtain ⟨S, S₁, hSF, hScard, hS₁card, hz₁, haR, Φ, hΦ⟩ :=
    exists_partner_root T θ (show S₀.card ≤ 4 by omega) ha hg haz hf
  have hLz := le_cent_single T.std T.cyc
  have hSc : 2 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  obtain ⟨hz₁', hc₁⟩ := caseIAt_transport_of_le hLz θ (show S₀.card = S₁.card by omega) hSc hI
  obtain ⟨hzS, hcS⟩ := caseIAt_transport_of_le hLz θ (show S₀.card = S.card by omega) hSc hI
  set zb : Sec G (corr (X := G) θ (altSub S)) := QuotientGroup.mk ⟨z, hzS⟩ with hzb
  set ab : Sec G (corr (X := G) θ (altSub S)) := QuotientGroup.mk ⟨a, haR⟩ with hab
  have hz2 : z * z = 1 := T.cyc.mul_self
  have haa : a * a = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hac : ab ∈ Subgroup.center (Sec G (corr (X := G) θ (altSub S))) := by
    rw [← hΦ, Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := Φ.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hc₁) y']
  obtain ⟨σ, hσf⟩ := exists_ofSubtype_eq (fun i hi => mem_fixFin.1 (hSF hi))
  have hθc : thetaHom T θ S σ ∈ Subgroup.center (Sec G (corr (X := G) θ (altSub S))) := by
    obtain ⟨y, hy, hyR, hyab⟩ := mk_eq_conj_thetaHom_or T θ ha haa hσf haR hzS
    rw [← hab, ← hzb] at hyab
    set yb : Sec G (corr (X := G) θ (altSub S)) := QuotientGroup.mk ⟨y, hyR⟩ with hyb
    have hconj : ∀ t : Sec G (corr (X := G) θ (altSub S)), ab = yb * t * yb⁻¹ →
        t ∈ Subgroup.center (Sec G (corr (X := G) θ (altSub S))) := by
      intro t ht
      have : t = ab := by
        have h1 : t = yb⁻¹ * ab * yb := by rw [ht]; group
        rw [h1, (Subgroup.mem_center_iff.1 hac) yb⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      rw [this]
      exact hac
    rcases hyab with h1 | h1
    · exact hconj _ h1
    · have h2 := hconj _ h1
      have : thetaHom T θ S σ = zb⁻¹ * (zb * thetaHom T θ S σ) := by group
      rw [this]
      exact mul_mem (inv_mem hcS) h2
  have hSc5 : 5 ≤ Sᶜ.card := by rw [card_compl_fin]; omega
  have hσ1 : σ = 1 := by
    refine eq_one_of_forall_commute (by simp only [Fintype.card_coe]; omega) fun π => ?_
    apply thetaHom_injective T θ hSc5
    rw [map_mul, map_mul]
    exact ((Subgroup.mem_center_iff.1 hθc) (thetaHom T θ S π)).symm
  have hp1 : permOf T.toBase θ ha = 1 := by rw [← hσf, hσ1, map_one]
  have haK := (permOf_eq_one_iff T.toBase θ ha).1 hp1
  have haz' : a ∈ zpowers z :=
    mem_zpowers_of_two_pow T.cyc T.card ⟨haK, ha⟩ (k := 1) (by rw [pow_one, pow_two]; exact haa)
  have haQ : a ∈ Q := by rw [eq_zpowers_of_card_eq_two_of_cyc T.cyc T.card]; exact haz'
  rcases eq_one_or_eq_of_card_eq_two T.cyc T.card haQ with h1 | h1
  · have hz1 : z = 1 := by
      have : g * z * g⁻¹ = 1 := hg.trans h1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    have := T.cyc.order
    rw [hz1, orderOf_one] at this
    exact absurd this (by decide)
  · exact haz h1

end Near

section Twist

theorem section_swap_of_near_partner (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S₀ : Finset (Fin n)} (hkn : S₀.card + 7 ≤ n) (hII : CaseIIAt θ z S₀) {a g : G}
    (ha : a ∈ centralizer ({z} : Set G)) (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf T.toBase θ ha)).card ∧ (fixFin (permOf T.toBase θ ha)).card ≠ 6)
    {S : Finset (Fin n)} (hSF : S ⊆ fixFin (permOf T.toBase θ ha)) (hS : S.card = S₀.card)
    (haR : a ∈ centralizer (corr (X := G) θ (altSub S) : Set G))
    (ε : Perm (Fin (n - S.card + 2)) ≃* Sec G (corr (X := G) θ (altSub S))) :
    (ε.symm (QuotientGroup.mk ⟨a, haR⟩)).IsSwap := by
  obtain ⟨S₁, hS₁card, hz₁, haR', Φ, hΦ⟩ := exists_partner_root_at T θ ha hg haz hf hSF
  have hSc : 2 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  obtain ⟨hz₁', hs₁⟩ := caseIIAt_transport_of_le (le_cent_single T.std T.cyc) θ
    (show S₀.card = S₁.card by omega) hSc hII
  have hsa : SymOutcome (QuotientGroup.mk ⟨a, haR⟩ : Sec G (corr (X := G) θ (altSub S)))
      (n - S.card) := by
    have := SymOutcome.map' Φ hs₁
    rw [hΦ, hS₁card] at this
    exact this
  obtain ⟨ε', hε'⟩ := hsa
  have := isSwap_map_of_mulEquiv (ε'.trans ε.symm) rfl
    (by simp only [Fintype.card_fin]; omega) hε'
  simpa using this

omit [Finite G] in
private theorem card_fixFin_of_isSwap' {σ : Perm (Fin n)} (hσ : σ.IsSwap) :
    (fixFin σ).card = n - 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => σ i = i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hs : σ.support = Finset.univ.filter (fun i => ¬ σ i = i) := by
    ext i
    simp [Perm.mem_support]
  have h2 : (fixFin σ).card + σ.support.card = n := by
    rw [hs]
    exact h
  rw [Perm.card_support_eq_two.2 hσ] at h2
  omega

private theorem not_isSwap_mul_of_comm' {α : Type*} [DecidableEq α] [Fintype α]
    {σ₁ σ₂ : Perm α} (h₁ : σ₁.IsSwap) (h₂ : σ₂.IsSwap) (hc : σ₁ * σ₂ = σ₂ * σ₁)
    (hne : σ₁ ≠ σ₂) : ¬ (σ₁ * σ₂).IsSwap := by
  intro h3
  have hd : σ₁.Disjoint σ₂ := by
    intro i
    by_cases hi : σ₂ i = i
    · exact Or.inr hi
    · left
      exact fixes_of_comm_swap h₂ h₁ hc hne hi
  have hcard := hd.card_support_mul
  rw [Perm.card_support_eq_two.2 h₁, Perm.card_support_eq_two.2 h₂,
    Perm.card_support_eq_two.2 h3] at hcard
  omega

theorem not_isConj_both (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hII : CaseIIAt θ z S₀) {τ : Perm (Fin n)} (hτ : τ.IsSwap) :
    ¬ (IsConj z (swapIota T θ τ : G) ∧ IsConj z (z * (swapIota T θ τ : G))) := by
  classical
  rintro ⟨h₁, h₂⟩
  have hz2 : z * z = 1 := T.cyc.mul_self
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hsC := swapIota_mem_centralizer T θ τ
  have hzsC := mul_mem hzC hsC
  have hps : permOf T.toBase θ hsC = τ := permOf_swapIota T θ τ
  have hpz : permOf T.toBase θ hzC = 1 := (permOf_eq_one_iff T.toBase θ hzC).2 (T.cyc.le T.cyc.mem)
  have hpzs : permOf T.toBase θ hzsC = τ := by
    rw [permOf_mul T.toBase θ hzC hsC hzsC, hpz, one_mul, hps]
  have hfix : (fixFin τ).card = n - 2 := card_fixFin_of_isSwap' hτ
  obtain ⟨S, hSF, hScard⟩ := Finset.exists_subset_card_eq
    (show S₀.card ≤ (fixFin τ).card by omega)
  have hSc : 2 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  obtain ⟨hzS, ε, hε⟩ := caseIIAt_transport_of_le (le_cent_single T.std T.cyc) θ
    (show S₀.card = S.card by omega) hSc hII
  have hsz : (swapIota T θ τ : G) ≠ z := fun h' => T.z_notMem (h' ▸ (swapIota T θ τ).2)
  have hzsz : z * (swapIota T θ τ : G) ≠ z := by
    intro h'
    have h1 : (swapIota T θ τ : G) = 1 := by
      calc (swapIota T θ τ : G) = z⁻¹ * (z * (swapIota T θ τ : G)) := by group
        _ = 1 := by rw [h', inv_mul_cancel]
    have h2 := hps
    rw [permOf_congr T.toBase θ h1 hsC (one_mem _), permOf_one] at h2
    obtain ⟨p, q, hpq, hτe⟩ := hτ
    rw [← h2] at hτe
    have := congrArg (fun f : Perm (Fin n) => f p) hτe
    simp only [Perm.one_apply, swap_apply_left] at this
    exact hpq this
  have hsR : (swapIota T θ τ : G) ∈ centralizer (corr (X := G) θ (altSub S) : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (comm_of_mem_corr_of_permOf_fix T.toBase θ hsC
      (fun i hi => by rw [hps]; exact mem_fixFin.1 (hSF hi)) hw).symm
  have hzsR := mul_mem hzS hsR
  have hfτ : 5 ≤ (fixFin τ).card ∧ (fixFin τ).card ≠ 6 := ⟨by omega, by omega⟩
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 h₁
  obtain ⟨g₂, hg₂⟩ := isConj_iff.1 h₂
  have hsw₁ := section_swap_of_near_partner T θ hkn hII hsC hg₁ hsz
    (by rw [hps]; exact hfτ) (by rw [hps]; exact hSF) (by omega) hsR ε
  have hsw₂ := section_swap_of_near_partner T θ hkn hII hzsC hg₂ hzsz
    (by rw [hpzs]; exact hfτ) (by rw [hpzs]; exact hSF) (by omega) hzsR ε
  have hprod : ε.symm (QuotientGroup.mk ⟨z * (swapIota T θ τ : G), hzsR⟩) =
      ε.symm (QuotientGroup.mk ⟨z, hzS⟩) *
        ε.symm (QuotientGroup.mk ⟨(swapIota T θ τ : G), hsR⟩) := by
    rw [← map_mul, ← QuotientGroup.mk_mul]
    rfl
  have hcomm : ε.symm (QuotientGroup.mk ⟨z, hzS⟩) *
        ε.symm (QuotientGroup.mk ⟨(swapIota T θ τ : G), hsR⟩) =
      ε.symm (QuotientGroup.mk ⟨(swapIota T θ τ : G), hsR⟩) *
        ε.symm (QuotientGroup.mk ⟨z, hzS⟩) := by
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hsC).symm
  have hss := swapIota_mul_self T θ (show τ * τ = 1 by
    obtain ⟨p, q, _, hτe⟩ := hτ
    rw [hτe, swap_mul_self])
  have hne : ε.symm (QuotientGroup.mk ⟨z, hzS⟩) ≠
      ε.symm (QuotientGroup.mk ⟨(swapIota T θ τ : G), hsR⟩) :=
    fun h' => mk_ne_of_partner T.cyc hsC hsz hss hzS hsR (ε.symm.injective h').symm
  exact not_isSwap_mul_of_comm' hε hsw₁ hcomm hne (hprod ▸ hsw₂)

theorem exists_swap_partner (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S₀ : Finset (Fin n)} (hkn : S₀.card + 7 ≤ n) (hII : CaseIIAt θ z S₀) :
    ∃ τ : Perm (Fin n), τ.IsSwap ∧
      (IsConj z (swapIota T θ τ : G) ∨ IsConj z (z * (swapIota T θ τ : G))) := by
  classical
  obtain ⟨hzS, ε, hε⟩ := hII
  set R := corr (X := G) θ (altSub S₀) with hR
  set zb : Sec G R := QuotientGroup.mk ⟨z, hzS⟩ with hzb
  have hz2 : z * z = 1 := T.cyc.mul_self
  have hzb2 : zb * zb = 1 := mk_z_mul_self T.toBase hzS
  have hSc5 : 5 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  have hScn : S₀ᶜ.card = n - S₀.card := card_compl_fin S₀
  set Ψ : Perm ↥S₀ᶜ →* Perm (Fin (n - S₀.card + 2)) :=
    ε.symm.toMonoidHom.comp (thetaHom T θ S₀) with hΨ
  have hinj : Function.Injective Ψ :=
    ε.symm.injective.comp (thetaHom_injective T θ hSc5)
  have hcomm : ∀ π, Ψ π * ε.symm zb = ε.symm zb * Ψ π := by
    intro π
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, thetaHom_comm_z T θ S₀ hzS π]
  have hneΨ : ∀ π, Ψ π ≠ ε.symm zb := by
    intro π hπ
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hπ
    exact thetaHom_ne_z T θ S₀ hzS π (ε.symm.injective hπ)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (show 1 < S₀ᶜ.card by omega)
  set σ₀ : Perm ↥S₀ᶜ := swap ⟨i, hi⟩ ⟨j, hj⟩ with hσ₀
  have hσ₀s : σ₀.IsSwap := ⟨⟨i, hi⟩, ⟨j, hj⟩, fun h' => hij (congrArg Subtype.val h'), rfl⟩
  obtain ⟨τ', hτ's, -, hτ'ne, hΨσ⟩ := embedding_swap_cases (α := ↥S₀ᶜ)
    (β := Fin (n - S₀.card + 2)) (by simp only [Fintype.card_fin, Fintype.card_coe]; omega)
    (by simp only [Fintype.card_coe]; omega) Ψ hinj hε hcomm hneΨ hσ₀s
  obtain ⟨p₀, q₀, hpq₀, hτ₀e⟩ := hε
  obtain ⟨r₀, s₀, hrs₀, hτ'e⟩ := hτ's
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hpq₀ hrs₀)
  have hετ' : ε τ' = ε c * zb * (ε c)⁻¹ := by
    rw [hτ'e, ← hc, ← hτ₀e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hκR := kappa_mem_centralizer_root T θ S₀ σ₀
  have hzκR := mul_mem hzS hκR
  have hκC := kappa_mem_centralizer T θ S₀ σ₀
  have hκ2 : kappa T θ S₀ σ₀ * kappa T θ S₀ σ₀ = 1 :=
    swapIota_mul_self T θ (by rw [← map_mul, hσ₀, swap_mul_self, map_one])
  have hzκ : z * kappa T θ S₀ σ₀ = kappa T θ S₀ σ₀ * z :=
    (mem_centralizer_singleton_iff.1 hκC).symm
  obtain ⟨b, hbR, hb2, hbmk, hbcases⟩ : ∃ (b : G) (hbR : b ∈ centralizer (R : Set G)), b * b = 1 ∧
      (QuotientGroup.mk ⟨b, hbR⟩ : Sec G R) = ε τ' ∧
        (b = kappa T θ S₀ σ₀ ∨ b = z * kappa T θ S₀ σ₀) := by
    rcases hΨσ with h1 | h1
    · refine ⟨kappa T θ S₀ σ₀, hκR, hκ2, ?_, Or.inl rfl⟩
      have h2 : ε (Ψ σ₀) = ε τ' := by rw [h1]
      simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply] at h2
      rw [← h2, thetaHom_apply]
    · refine ⟨z * kappa T θ S₀ σ₀, hzκR, ?_, ?_, Or.inr rfl⟩
      · calc z * kappa T θ S₀ σ₀ * (z * kappa T θ S₀ σ₀) =
            (z * z) * (kappa T θ S₀ σ₀ * kappa T θ S₀ σ₀) := by
              rw [mul_assoc, ← mul_assoc (kappa T θ S₀ σ₀) z (kappa T θ S₀ σ₀), ← hzκ]
              group
          _ = 1 := by rw [hz2, hκ2, one_mul]
      · have h2 : ε (Ψ σ₀) = ε (ε.symm zb * τ') := by rw [h1]
        simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply, map_mul] at h2
        have h3 : (QuotientGroup.mk ⟨z * kappa T θ S₀ σ₀, hzκR⟩ : Sec G R) =
            zb * thetaHom T θ S₀ σ₀ := by
          rw [thetaHom_apply, hzb, ← QuotientGroup.mk_mul]
          rfl
        rw [h3, h2, ← mul_assoc, hzb2, one_mul]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (ε c)
  set u₀ : ↥(centralizer (R : Set G)) := y * ⟨z, hzS⟩ * y⁻¹ with hu₀
  have hu₀2 : u₀ * u₀ = 1 := by
    rw [hu₀]
    have : (⟨z, hzS⟩ : ↥(centralizer (R : Set G))) * ⟨z, hzS⟩ = 1 := Subtype.ext hz2
    calc y * ⟨z, hzS⟩ * y⁻¹ * (y * ⟨z, hzS⟩ * y⁻¹) =
        y * ((⟨z, hzS⟩ : ↥(centralizer (R : Set G))) * ⟨z, hzS⟩) * y⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hb2' : (⟨b, hbR⟩ : ↥(centralizer (R : Set G))) * ⟨b, hbR⟩ = 1 := Subtype.ext hb2
  have hmk : (QuotientGroup.mk u₀ : Sec G R) = QuotientGroup.mk ⟨b, hbR⟩ := by
    rw [hbmk, hετ', hu₀, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy]
  have hmem : (⟨b, hbR⟩ : ↥(centralizer (R : Set G))) * u₀ ∈
      CFSG.oddCore ↥(centralizer (R : Set G)) := by
    have h1 := QuotientGroup.eq.1 hmk.symm
    have hbinv : (⟨b, hbR⟩ : ↥(centralizer (R : Set G)))⁻¹ = ⟨b, hbR⟩ :=
      inv_eq_of_mul_eq_one_right hb2'
    rwa [hbinv] at h1
  obtain ⟨r, -, hr⟩ := exists_conj_of_involutions_of_mul_mem
    (fun x hx => orderOf_odd_of_mem_oddCore hx) hu₀2 hb2' hmem
  have hconj : IsConj z b := by
    refine isConj_iff.2 ⟨((r * y : ↥(centralizer (R : Set G))) : G), ?_⟩
    have := congrArg Subtype.val hr
    simp only [hu₀, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    simp [mul_assoc]
  refine ⟨Perm.ofSubtype σ₀, hσ₀s.of_subtype_isSwap, ?_⟩
  rcases hbcases with rfl | rfl
  · exact Or.inl (by rw [kappa_apply] at hconj; exact hconj)
  · exact Or.inr (by rw [kappa_apply] at hconj; exact hconj)

theorem caseII_twist (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hII : CaseIIAt θ z S₀) :
    ∃ c : G, (c = 1 ∨ c = z) ∧ ∀ τ : Perm (Fin n), τ.IsSwap →
      IsConj z (c * (swapIota T θ τ : G)) ∧ ¬ IsConj z (z * c * (swapIota T θ τ : G)) := by
  classical
  have hz2 : z * z = 1 := T.cyc.mul_self
  obtain ⟨τ₀, hτ₀, hc₀⟩ := exists_swap_partner T θ hkn hII
  have key : ∀ c : G, (c = 1 ∨ c = z) → IsConj z (c * (swapIota T θ τ₀ : G)) →
      ∀ τ : Perm (Fin n), τ.IsSwap → IsConj z (c * (swapIota T θ τ : G)) := by
    intro c hc h0 τ hτ
    obtain ⟨p, q, hpq, hτ₀e⟩ := hτ₀
    obtain ⟨r, t, hrt, hτe⟩ := hτ
    obtain ⟨π, hπ⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hpq hrt)
    have hιτ : (swapIota T θ τ : G) = (swapIota T θ π : G) *
        (swapIota T θ τ₀ : G) * (swapIota T θ π : G)⁻¹ := by
      rw [hτe, ← hπ, ← hτ₀e, map_mul, map_mul, map_inv]
      rfl
    have hcπ : c * (swapIota T θ π : G) = (swapIota T θ π : G) * c := by
      rcases hc with rfl | rfl
      · simp
      · exact swapIota_comm_z T θ π
    refine h0.trans (isConj_iff.2 ⟨(swapIota T θ π : G), ?_⟩)
    rw [hιτ]
    calc (swapIota T θ π : G) * (c * (swapIota T θ τ₀ : G)) * (swapIota T θ π : G)⁻¹ =
        ((swapIota T θ π : G) * c) * (swapIota T θ τ₀ : G) * (swapIota T θ π : G)⁻¹ := by
          group
      _ = (c * (swapIota T θ π : G)) * (swapIota T θ τ₀ : G) * (swapIota T θ π : G)⁻¹ := by
          rw [hcπ]
      _ = c * ((swapIota T θ π : G) * (swapIota T θ τ₀ : G) * (swapIota T θ π : G)⁻¹) := by
          group
  have hnot : ∀ τ : Perm (Fin n), τ.IsSwap →
      ¬ (IsConj z (swapIota T θ τ : G) ∧ IsConj z (z * (swapIota T θ τ : G))) :=
    fun τ hτ => not_isConj_both T θ hk hkn hII hτ
  rcases hc₀ with h0 | h0
  · have h0' : IsConj z (1 * (swapIota T θ τ₀ : G)) := by rw [one_mul]; exact h0
    refine ⟨1, Or.inl rfl, fun τ hτ => ⟨key 1 (Or.inl rfl) h0' τ hτ, ?_⟩⟩
    intro h1
    rw [mul_one] at h1
    have h2 := key 1 (Or.inl rfl) h0' τ hτ
    rw [one_mul] at h2
    exact hnot τ hτ ⟨h2, h1⟩
  · refine ⟨z, Or.inr rfl, fun τ hτ => ⟨key z (Or.inr rfl) h0 τ hτ, ?_⟩⟩
    intro h1
    rw [hz2, one_mul] at h1
    exact hnot τ hτ ⟨h1, key z (Or.inr rfl) h0 τ hτ⟩

end Twist

section CaseII

@[expose] def CaseIIW (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (S : Subgroup G) (z : G) :
    Prop :=
  ∀ a : G, a ∈ Partners z ↔
    ∃ y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)),
      ∃ s ∈ S, IsSwapOn θ hn s ∧ a = y * s * y⁻¹

theorem caseIIW_of_untwisted (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hsw : ∀ (a : G) (ha : a ∈ centralizer ({z} : Set G)), a ∈ Partners z →
      (permOf T.toBase θ ha).IsSwap)
    (htw : ∀ τ : Perm (Fin n), τ.IsSwap →
      IsConj z (swapIota T θ τ : G) ∧ ¬ IsConj z (z * (swapIota T θ τ : G))) :
    CaseIIW θ T.hn (L ⊔ zpowers u) z := by
  intro a
  have hz2 : z * z = 1 := T.cyc.mul_self
  constructor
  · intro hP
    have ha : a ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hP.2.2
    have hs := hsw a ha hP
    have haa : a * a = 1 := Partners.mul_self_of hP hz2
    obtain ⟨y, hy, h | h⟩ := exists_oddY_conj_swapIota T θ ha haa
    · refine ⟨y, hy, _, (swapIota T θ (permOf T.toBase θ ha)).2,
        ⟨cent_le_normalizer T.std T.cyc (swapIota_mem_centralizer T θ _), ?_⟩, h⟩
      have := permOf_swapIota T θ (permOf T.toBase θ ha)
      rw [← this] at hs
      exact hs
    · exfalso
      apply (htw _ hs).2
      refine hP.1.trans (isConj_iff.2 ⟨y⁻¹, ?_⟩)
      calc y⁻¹ * a * y⁻¹⁻¹ =
          y⁻¹ * (y * (z * (swapIota T θ (permOf T.toBase θ ha) : G)) * y⁻¹) * y⁻¹⁻¹ :=
            congrArg (fun w => y⁻¹ * w * y⁻¹⁻¹) h
        _ = z * (swapIota T θ (permOf T.toBase θ ha) : G) := by group
  · rintro ⟨y, hy, s, hsS, ⟨hsN, hsw'⟩, rfl⟩
    have hsC := T.le_centralizer hsS
    have hyC := oddY_le_centralizer_z T.cyc hy
    have hιs : (swapIota T θ (permOf T.toBase θ hsC) : G) = s := by
      have : permOf T.toBase θ hsC = rhoSwap T θ ⟨s, hsS⟩ := rfl
      rw [this, swapIota_rhoSwap]
    have hs : (permOf T.toBase θ hsC).IsSwap := hsw'
    have hzs : IsConj z s := by
      have := (htw _ hs).1
      rwa [hιs] at this
    refine ⟨hzs.trans (isConj_iff.2 ⟨y, rfl⟩), ?_, ?_⟩
    · intro h
      apply T.z_notMem
      have : s = y⁻¹ * z * y := by rw [← h]; group
      have hyz : y⁻¹ * z * y = z := by
        rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hyC]
        group
      rw [← hyz, ← this]
      exact hsS
    · exact mem_centralizer_singleton_iff.1 (mul_mem (mul_mem hyC hsC) (inv_mem hyC))

theorem Shape.mul_z (T : Shape G L Q n z u) : Shape G L Q n z (u * z) := by
  have hcomm : u * z = z * u := mem_centralizer_singleton_iff.1 T.cent
  have hz2 : z ^ 2 = 1 := by rw [← T.cyc.order]; exact pow_orderOf_eq_one z
  refine ⟨T.toBase, mem_centralizer_singleton_iff.2 ?_, ?_, ?_⟩
  · calc u * z * z = (z * u) * z := by rw [hcomm]
      _ = z * (u * z) := mul_assoc _ _ _
  · intro hmem
    apply T.outer
    have hzK : z ∈ L ⊔ centralizer (L : Set G) := mem_sup_right (T.cyc.le T.cyc.mem)
    have := mul_mem hmem (inv_mem hzK)
    simpa [mul_assoc] using this
  · rw [(Commute.mul_pow hcomm 2), T.sq, hz2, one_mul]

theorem swapIota_mul_z_eq (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {τ : Perm (Fin n)} (hτ : sign τ = -1) :
    (swapIota T.mul_z θ τ : G) = z * (swapIota T θ τ : G) := by
  have huN := T.mem_normalizer
  have hsS := (swapIota T θ τ).2
  have hsC := swapIota_mem_centralizer T θ τ
  have hps := permOf_swapIota T θ τ
  have hsu : (swapIota T θ τ : G) * u ∈ L := by
    rcases (mem_or_mul_mem_of_mem_complement huN T.sq hsS) with h1 | h1
    · exfalso
      have h2 := permOf_of_mem T.toBase θ hsC h1
      rw [hps] at h2
      have h3 := mem_alternatingGroup.1 (θ ⟨_, h1⟩).2
      rw [← h2, hτ] at h3
      exact absurd h3 (by decide)
    · exact h1
  have hu1 : u * u = 1 := by rw [← pow_two, T.sq]
  have hzs : z * (swapIota T θ τ : G) = (swapIota T θ τ : G) * u * (u * z) := by
    calc z * (swapIota T θ τ : G) = (swapIota T θ τ : G) * z := swapIota_comm_z T θ τ
      _ = (swapIota T θ τ : G) * (u * u) * z := by rw [hu1, mul_one]
      _ = (swapIota T θ τ : G) * u * (u * z) := by group
  have hmem : z * (swapIota T θ τ : G) ∈ L ⊔ zpowers (u * z) := by
    rw [hzs]
    exact mul_mem (mem_sup_left hsu) (mem_sup_right (mem_zpowers _))
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hrho : rhoSwap T.mul_z θ ⟨_, hmem⟩ = τ := by
    show permOf T.toBase θ (mul_mem hzC hsC) = τ
    rw [permOf_mul T.toBase θ hzC hsC (mul_mem hzC hsC), hps,
      (permOf_eq_one_iff T.toBase θ hzC).2 (T.cyc.le T.cyc.mem), one_mul]
  have h1 := swapIota_rhoSwap T.mul_z θ ⟨_, hmem⟩
  rw [hrho] at h1
  rw [h1]

end CaseII

end CFSG.OddStandard.AltStdCycTwo.Two

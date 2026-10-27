module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
public import CFSG.RankThree.PerfectCover.HopfFormula

public import CFSG.GroupTheory.BurnsideNormalComplement



public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open Subgroup CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

@[expose] def QClean (q : ℕ) (S : Type) [Group S] : Prop :=
  ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (p : E →* S),
    Function.Surjective p → p.ker ≤ Subgroup.center E → ¬ q ∣ Nat.card p.ker

theorem qClean_of_not_dvd_hopf (q : ℕ) (S : Type) [Group S] [Finite S] [Group.IsPerfect S]
    (h : ¬ q ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S)) : QClean q S := by
  intro E _ _ _ p hp hC hdvd
  obtain ⟨-, ⟨h', -, -, -, -, e, -⟩, -, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_schur_multiplier p hp hC
  rw [← Nat.card_congr e.toEquiv] at hdvd
  exact h (hdvd.trans (Subgroup.card_quotient_dvd_card _))

theorem QClean.congr {q : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (h : QClean q S) :
    QClean q S' := by
  intro E _ _ _ p' hp' hC' hdvd
  have hsurj : Function.Surjective (e.symm.toMonoidHom.comp p') := fun s => by
    obtain ⟨x, hx⟩ := hp' (e s)
    exact ⟨x, by simp [hx]⟩
  have hker : (e.symm.toMonoidHom.comp p').ker = p'.ker := by
    ext x
    simp
  have hnd := h E (e.symm.toMonoidHom.comp p') hsurj ((le_of_eq hker).trans hC')
  rw [hker] at hnd
  exact hnd hdvd

theorem quotCenter_mulEquiv {Y : Type} [Group Y] {L₁ L₂ : Subgroup Y} (g : Y)
    (h : L₁.map (MulAut.conj g).toMonoidHom = L₂) :
    Nonempty ((↥L₁ ⧸ Subgroup.center ↥L₁) ≃* (↥L₂ ⧸ Subgroup.center ↥L₂)) := by
  subst h
  let e₀ := Subgroup.equivMapOfInjective L₁ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact ⟨QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)⟩

theorem exists_orderOf_eq_of_dvd_quot {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {q : ℕ}
    (hq : q.Prime) (h : q ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) : ∃ t ∈ L, orderOf t = q := by
  haveI := Fact.mk hq
  have hdvd : q ∣ Nat.card ↥L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)]
    exact h.mul_right _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hdvd
  exact ⟨x.1, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem qClean_exists_noncentral {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {q : ℕ}
    (hq : q.Prime) (hqs : IsQuasisimple ↥L) (hcl : QClean q (↥L ⧸ Subgroup.center ↥L)) {t : Y}
    (ht : t ∈ L) (ho : orderOf t = q) : ∃ l ∈ L, l * t ≠ t * l := by
  by_contra hcon
  have hcomm : ∀ l ∈ L, l * t = t * l := fun l hl => by
    by_contra hne
    exact hcon ⟨l, hl, hne⟩
  obtain ⟨hperf, -⟩ := hqs
  haveI : Group.IsPerfect ↥L := hperf
  have hcen : (⟨t, ht⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g.1 g.2)
  have hdvd : q ∣ Nat.card (Subgroup.center ↥L) := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hcen
    rwa [Subgroup.orderOf_mk, ho] at h1
  have hnd := hcl ↥L (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' (Subgroup.center ↥L)).le
  rw [QuotientGroup.ker_mk'] at hnd
  exact hnd hdvd

theorem bh_commutatorElement_mul_of_comm {W : Type*} [Group W] (a g k : W)
    (hz : g * ⁅a, k⁆ = ⁅a, k⁆ * g) : ⁅a, g * k⁆ = ⁅a, g⁆ * ⁅a, k⁆ := by
  calc ⁅a, g * k⁆ = ⁅a, g⁆ * (g * ⁅a, k⁆ * g⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, g⁆ * ⁅a, k⁆ := by rw [hz, mul_inv_cancel_right]

theorem commute_of_commutator_mem {W : Type*} [Group W] (G Z : Subgroup W) (hG : ⁅G, G⁆ = G)
    (hZc : Z ≤ Subgroup.centralizer (G : Set W)) (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (a : W) (h : ∀ b ∈ G, ⁅a, b⁆ ∈ Z) : ∀ b ∈ G, a * b = b * a := by
  have hZG : ∀ z ∈ Z, ∀ g ∈ G, g * z = z * g := fun z hz g hg =>
    Subgroup.mem_centralizer_iff.mp (hZc hz) g hg
  have hmul : ∀ g ∈ G, ∀ k ∈ G, ⁅a, g * k⁆ = ⁅a, g⁆ * ⁅a, k⁆ := fun g hg k hk =>
    bh_commutatorElement_mul_of_comm a g k (hZG _ (h k hk) g hg)
  obtain ⟨φ, hφ⟩ : ∃ φ : G →* Z, ∀ g : G, ((φ g : Z) : W) = ⁅a, (g : W)⁆ :=
    ⟨MonoidHom.mk' (fun g : G => (⟨⁅a, (g : W)⁆, h g g.2⟩ : Z))
      (fun g k => Subtype.ext (hmul g g.2 k k.2)), fun g => rfl⟩
  have hkey : ∀ x ∈ G, ∀ y ∈ G, ⁅a, ⁅x, y⁆⁆ = 1 := by
    intro x hx y hy
    have hc : φ ⁅(⟨x, hx⟩ : G), ⟨y, hy⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subtype.ext (hZab _ (φ ⟨x, hx⟩).2 _ (φ ⟨y, hy⟩).2))
    have h1 : ((φ ⁅(⟨x, hx⟩ : G), ⟨y, hy⟩⁆ : Z) : W) = ((1 : Z) : W) :=
      congrArg Subtype.val hc
    rw [hφ] at h1
    exact h1
  have hC : ⁅G, G⁆ ≤ Subgroup.centralizer ({a} : Set W) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    rw [Set.mem_singleton_iff.mp hc]
    exact commutatorElement_eq_one_iff_mul_comm.mp (hkey x hx y hy)
  rw [hG] at hC
  intro b hb
  exact Subgroup.mem_centralizer_iff.mp (hC hb) a (Set.mem_singleton a)

theorem perfect_of_quasisimple {Y : Type} [Group Y] {L : Subgroup Y} (h : IsQuasisimple ↥L) :
    ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.mp h.1

theorem exists_minimal_subgroup {G : Type*} [Group G] [Finite G] (P : Subgroup G → Prop)
    (h : ∃ J, P J) : ∃ J, P J ∧ ∀ J', P J' → J' ≤ J → J' = J := by
  obtain ⟨J, hJ, hmin⟩ := exists_minimal_of_wellFoundedLT P h
  exact ⟨J, hJ, fun J' hJ' hle => le_antisymm hle (hmin hJ' hle)⟩

theorem exists_perfect_cover {W Y : Type} [Group W] [Finite W] [Group Y] (ε : W →* Y)
    {L : Subgroup Y} (hL : L ≤ ε.range) (hp : ⁅L, L⁆ = L) :
    ∃ P : Subgroup W, P.map ε = L ∧ ⁅P, P⁆ = P := by
  have hne : ∃ P : Subgroup W, P.map ε = L :=
    ⟨L.comap ε, by rw [Subgroup.map_comap_eq, inf_eq_right.mpr hL]⟩
  obtain ⟨P, hP, hmin⟩ := exists_minimal_subgroup (fun P : Subgroup W => P.map ε = L) hne
  have hPL : P.map ε = L := hP
  have hle : ⁅P, P⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
  have hmap : (⁅P, P⁆).map ε = L := by
    rw [Subgroup.map_commutator, hPL, hp]
  exact ⟨P, hPL, hmin ⁅P, P⁆ hmap hle⟩

theorem cz_zpowers_le {W : Type} [Group W] {S : Set W} {x : W} (hx : x ∈ S) :
    zpowers x ≤ closure S :=
  Subgroup.zpowers_le.mpr (Subgroup.subset_closure hx)

theorem cz_step {W : Type} [Group W] [Finite W] {q : ℕ} (hq : q.Prime) {E : Subgroup W}
    (hE : IsElemAbelian q E) {d : W} (hdc : E ≤ Subgroup.centralizer ({d} : Set W))
    (hdq : d ^ q = 1) (hd : d ∉ E) :
    IsElemAbelian q (E ⊔ zpowers d) ∧ Nat.card (E ⊔ zpowers d : Subgroup W) = q * Nat.card E := by
  haveI := Fact.mk hq
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hd E.one_mem
  have hdz : IsElemAbelian q (zpowers d) := CFSG.Open.isElemAbelian_zpowers hdq
  have hcomm : ∀ x ∈ E, x * d = d * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hdc hx)
  have hc : ∀ x ∈ E, ∀ y ∈ zpowers d, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x d from hcomm x hx) k).eq
  have hab : IsElemAbelian q (E ⊔ zpowers d) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE hdz hc
  have hcardz : Nat.card (zpowers d) = q := by
    rw [Nat.card_zpowers, orderOf_eq_prime hdq hd1]
  have hdisj : Disjoint E (zpowers d) := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxd
    by_contra hx1
    have hordx : orderOf x = q := orderOf_eq_prime (hE.2 x hxE) hx1
    have hcard : Nat.card (zpowers d) = Nat.card (zpowers x) := by
      rw [hcardz, Nat.card_zpowers, hordx]
    have heq : zpowers x = zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxd) hcard.le
    apply hd
    have hdx : d ∈ zpowers x := by
      rw [heq]
      exact Subgroup.mem_zpowers d
    exact (Subgroup.zpowers_le.mpr hxE) hdx
  have hnorm : zpowers d ≤ Subgroup.normalizer (E : Set W) := by
    have hcent : d ∈ Subgroup.centralizer (E : Set W) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hdc hh)
    exact Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (E : Set W) hcent)
  have hcard : Nat.card (E ⊔ zpowers d : Subgroup W) = Nat.card E * Nat.card (zpowers d) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E (zpowers d) hnorm hdisj
  refine ⟨hab, ?_⟩
  rw [hcard, hcardz, mul_comm]

theorem closure_three_elemAbelian {W : Type} [Group W] [Finite W] {q : ℕ} (hq : q.Prime)
    {a b c : W} (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha : orderOf a = q) (hb : orderOf b = q) (hc : orderOf c = q)
    (hb1 : b ∉ closure {a}) (hc1 : c ∉ closure {a, b}) :
    IsElemAbelian q (closure {a, b, c} : Subgroup W) ∧
      Nat.card (closure {a, b, c} : Subgroup W) = q ^ 3 := by
  have haq : a ^ q = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have hbq : b ^ q = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  have hcq : c ^ q = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one c
  have hza : IsElemAbelian q (zpowers a) := CFSG.Open.isElemAbelian_zpowers haq
  have hcza : Nat.card (zpowers a) = q := by
    rw [Nat.card_zpowers, ha]
  have cab : zpowers a ≤ Subgroup.centralizer ({b} : Set W) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hab)
  have cac : zpowers a ≤ Subgroup.centralizer ({c} : Set W) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hac)
  have cbc : zpowers b ≤ Subgroup.centralizer ({c} : Set W) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbc)
  have hdc3 : zpowers a ⊔ zpowers b ≤ Subgroup.centralizer ({c} : Set W) := sup_le cac cbc
  have hbza : b ∉ zpowers a := by
    rw [Subgroup.zpowers_eq_closure]
    exact hb1
  have hsub2 : zpowers a ⊔ zpowers b ≤ closure ({a, b} : Set W) :=
    sup_le (cz_zpowers_le (by simp)) (cz_zpowers_le (by simp))
  have hczab : c ∉ zpowers a ⊔ zpowers b := fun h => hc1 (hsub2 h)
  have hsub3 : zpowers a ⊔ zpowers b ⊔ zpowers c ≤ closure ({a, b, c} : Set W) :=
    sup_le (sup_le (cz_zpowers_le (by simp)) (cz_zpowers_le (by simp)))
      (cz_zpowers_le (by simp))
  have hcl : (closure ({a, b, c} : Set W) : Subgroup W) =
      zpowers a ⊔ zpowers b ⊔ zpowers c := by
    apply le_antisymm
    · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)),
        Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)),
        Subgroup.mem_sup_right (Subgroup.mem_zpowers c)⟩
    · exact hsub3
  obtain ⟨h2a, h2b⟩ := cz_step hq hza cab hbq hbza
  obtain ⟨h3a, h3b⟩ := cz_step hq h2a hdc3 hcq hczab
  rw [hcl]
  refine ⟨h3a, ?_⟩
  rw [h3b, h2b, hcza]
  ring

theorem cz_map_isElemAbelian {G : Type} [Group G] {q : ℕ} {G₁ : Subgroup G} {K : Type} [Group K]
    {E : Subgroup K} (hE : IsElemAbelian q E) (H' : Subgroup G₁) (φ : G₁ →* E)
    (hinj : ∀ x ∈ H', ∀ y ∈ H', φ x = φ y → x = y) :
    IsElemAbelian q (H'.map G₁.subtype) := by
  have hcommφ : ∀ x y : G₁, φ x * φ y = φ y * φ x := by
    intro x y
    apply Subtype.ext
    exact hE.comm (φ x).2 (φ y).2
  have hcommH : ∀ a ∈ H'.map G₁.subtype, ∀ b ∈ H'.map G₁.subtype, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    have h1 : x * y = y * x := hinj (x * y) (H'.mul_mem hx hy) (y * x) (H'.mul_mem hy hx)
      (by rw [map_mul, map_mul]; exact hcommφ x y)
    exact congrArg Subtype.val h1
  have hexpH : ∀ x ∈ H'.map G₁.subtype, x ^ q = 1 := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have hφq : φ (x' ^ q) = 1 := by
      rw [map_pow]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 _ (φ x').2
    have h1 : x' ^ q = 1 :=
      hinj (x' ^ q) (H'.pow_mem hx' q) 1 H'.one_mem (by rw [hφq, map_one])
    rw [← map_pow, h1, map_one]
  exact ⟨⟨⟨fun a b => Subtype.ext (hcommH _ a.2 _ b.2)⟩⟩, fun x hx => hexpH x hx⟩

theorem exists_elemAbelian_lift {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (C : Subgroup G) [C.Normal] (hCq : ¬ q ∣ Nat.card C) (E : Subgroup (G ⧸ C))
    (hE : IsElemAbelian q E) {k : ℕ} (hk : Nat.card E = q ^ k) :
    ∃ H : Subgroup G, IsElemAbelian q H ∧ Nat.card H = q ^ k := by
  let G₁ : Subgroup G := E.comap (QuotientGroup.mk' C)
  have hCG₁ : C ≤ G₁ := by
    intro c hc
    show QuotientGroup.mk' C c ∈ E
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff c).mpr hc]
    exact E.one_mem
  let φ : G₁ →* E := ((QuotientGroup.mk' C).comp G₁.subtype).codRestrict E (fun x => x.2)
  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e : G ⧸ C)
    have hgG₁ : g ∈ G₁ := by
      show QuotientGroup.mk' C g ∈ E
      rw [QuotientGroup.mk'_apply, hg]
      exact e.2
    exact ⟨⟨g, hgG₁⟩, Subtype.ext hg⟩
  have hker : φ.ker = C.subgroupOf G₁ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff (x : G)).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff (x : G)).mpr h)
  have hidx : (C.subgroupOf G₁).index = q ^ k := by
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφsurj, Subgroup.card_top, hk]
  have hcardN : Nat.card (C.subgroupOf G₁) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCG₁).toEquiv
  have hcop : Nat.Coprime (Nat.card (C.subgroupOf G₁)) (C.subgroupOf G₁).index := by
    rw [hcardN, hidx]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hq).2 hCq).symm
  obtain ⟨H', hcomp⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hH'card : Nat.card H' = q ^ k := by
    rw [← hcomp.symm.index_eq_card, hidx]
  have hinj : ∀ x ∈ H', ∀ y ∈ H', φ x = φ y → x = y := by
    intro x hx y hy hxy
    have hzN : x * y⁻¹ ∈ C.subgroupOf G₁ := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    have hzH : x * y⁻¹ ∈ H' := H'.mul_mem hx (H'.inv_mem hy)
    exact mul_inv_eq_one.mp (Subgroup.disjoint_def.mp hcomp.disjoint hzN hzH)
  refine ⟨H'.map G₁.subtype, cz_map_isElemAbelian hE H' φ hinj, ?_⟩
  rw [Subgroup.card_map_of_injective G₁.subtype_injective, hH'card]

theorem cover_inf_ker_eq_bot {W Y : Type} [Group W] [Finite W] [Group Y] [Finite Y] {q : ℕ}
    (ε : W →* Y) (hcen : ε.ker ≤ Subgroup.center W) (hpow : ∀ x ∈ ε.ker, ∃ n : ℕ, x ^ q ^ n = 1)
    (hq : q.Prime) {L : Subgroup Y} (hqs : IsQuasisimple ↥L)
    (hcl : QClean q (↥L ⧸ Subgroup.center ↥L)) {P : Subgroup W} (hP : ⁅P, P⁆ = P)
    (hPL : P.map ε = L) : P ⊓ ε.ker = ⊥ := by
  classical
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have hmem : ∀ x : ↥P, ε (x : W) ∈ L := fun x => hPL ▸ Subgroup.mem_map_of_mem ε x.2
  let f : ↥P →* ↥L := (ε.comp P.subtype).codRestrict L hmem
  let p : ↥P →* ↥L ⧸ Subgroup.center ↥L := (QuotientGroup.mk' (Subgroup.center ↥L)).comp f
  have hsurj : Function.Surjective p := by
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    have hl : (l : Y) ∈ P.map ε := hPL ▸ l.2
    obtain ⟨x, hxP, hx⟩ := Subgroup.mem_map.mp hl
    refine ⟨⟨x, hxP⟩, ?_⟩
    have hfx : f ⟨x, hxP⟩ = l := Subtype.ext hx
    show QuotientGroup.mk' (Subgroup.center ↥L) (f ⟨x, hxP⟩) = QuotientGroup.mk l
    rw [hfx]
    rfl
  have hker : p.ker ≤ Subgroup.center ↥P := by
    intro x hx
    have hxz : f x ∈ Subgroup.center ↥L := by
      have := (QuotientGroup.eq_one_iff (f x)).mp hx
      exact this
    rw [Subgroup.mem_center_iff]
    intro y
    have hxy : ∀ b ∈ P, ⁅(x : W), b⁆ ∈ ε.ker := by
      intro b hb
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      have := Subgroup.mem_center_iff.mp hxz ⟨ε b, hmem ⟨b, hb⟩⟩
      exact (congrArg Subtype.val this).symm
    have hcomm := commute_of_commutator_mem P ε.ker hP
      (fun z hz => by
        rw [Subgroup.mem_centralizer_iff]
        intro b _
        exact (Subgroup.mem_center_iff.mp (hcen hz) b))
      (fun a ha b _ => (Subgroup.mem_center_iff.mp (hcen ha) b).symm) (x : W) hxy y y.2
    exact Subtype.ext (hcomm.symm)
  have hnd := hcl ↥P p hsurj hker
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxP, hxk⟩ := hx
  rw [Subgroup.mem_bot]
  obtain ⟨n, hn⟩ := hpow x hxk
  have hxker : (⟨x, hxP⟩ : ↥P) ∈ p.ker := by
    show p ⟨x, hxP⟩ = 1
    have : f ⟨x, hxP⟩ = 1 := Subtype.ext (MonoidHom.mem_ker.mp hxk)
    show QuotientGroup.mk' (Subgroup.center ↥L) (f ⟨x, hxP⟩) = 1
    rw [this, map_one]
  set y : p.ker := ⟨⟨x, hxP⟩, hxker⟩ with hy
  have hyn : y ^ q ^ n = 1 := Subtype.ext (Subtype.ext hn)
  have h1 : orderOf y ∣ q ^ n := orderOf_dvd_of_pow_eq_one hyn
  have h2 : orderOf y ∣ Nat.card p.ker := orderOf_dvd_natCard y
  have hcop : Nat.Coprime (q ^ n) (Nat.card p.ker) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnd)
  have h3 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : y = 1 := orderOf_eq_one_iff.mp h3
  have h5 : ((y : ↥P) : W) = 1 := by rw [h4]; rfl
  exact h5

theorem cover_commute {W Y : Type} [Group W] [Group Y] (ε : W →* Y)
    (hcen : ε.ker ≤ Subgroup.center W) {P₁ P₂ : Subgroup W} (h₂ : ⁅P₂, P₂⁆ = P₂)
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, ε a * ε b = ε b * ε a) : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := by
  intro a ha
  refine commute_of_commutator_mem P₂ ε.ker h₂ ?_ ?_ a ?_
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact (Subgroup.mem_center_iff.mp (hcen hz) b)
  · intro x hx y _
    exact (Subgroup.mem_center_iff.mp (hcen hx) y).symm
  · intro b hb
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc a ha b hb

theorem exists_elemAbelian_of_cover {G Y : Type} [Group G] [Finite G] [Group Y] [Finite Y] {q : ℕ}
    (hq : q.Prime) (φ : G →* Y) (C : Subgroup G) [C.Normal] (hCq : ¬ q ∣ Nat.card C)
    (hCker : C ≤ φ.ker) (hcen : ∀ x ∈ φ.ker, ∀ y : G, ⁅x, y⁆ ∈ C)
    (hpow : ∀ x ∈ φ.ker, ∃ n : ℕ, x ^ q ^ n ∈ C)
    (L₁ L₂ L₃ : Subgroup Y) (hqs₁ : IsQuasisimple ↥L₁) (hqs₂ : IsQuasisimple ↥L₂)
    (hqs₃ : IsQuasisimple ↥L₃)
    (c12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (c13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a)
    (c23 : ∀ b ∈ L₂, ∀ c ∈ L₃, b * c = c * b)
    (hL₁ : L₁ ≤ φ.range) (hL₂ : L₂ ≤ φ.range) (hL₃ : L₃ ≤ φ.range)
    (hcl₁ : QClean q (↥L₁ ⧸ Subgroup.center ↥L₁)) (hcl₂ : QClean q (↥L₂ ⧸ Subgroup.center ↥L₂))
    (hcl₃ : QClean q (↥L₃ ⧸ Subgroup.center ↥L₃))
    (t₁ t₂ t₃ : Y) (h₁ : t₁ ∈ L₁) (h₂ : t₂ ∈ L₂) (h₃ : t₃ ∈ L₃)
    (o₁ : orderOf t₁ = q) (o₂ : orderOf t₂ = q) (o₃ : orderOf t₃ = q) :
    ∃ H : Subgroup G, IsElemAbelian q H ∧ Nat.card H = q ^ 3 := by
  classical
  let mk : G →* G ⧸ C := QuotientGroup.mk' C
  let ε : (G ⧸ C) →* Y := QuotientGroup.lift C φ hCker
  have hε : ∀ x : G, ε (mk x) = φ x := fun x => rfl
  have hmk : Function.Surjective mk := QuotientGroup.mk'_surjective C
  have hrange : ∀ {L : Subgroup Y}, L ≤ φ.range → L ≤ ε.range := by
    intro L hL y hy
    obtain ⟨x, hx⟩ := hL hy
    exact ⟨mk x, by rw [hε]; exact hx⟩
  have hkermem : ∀ w ∈ ε.ker, ∃ x ∈ φ.ker, mk x = w := by
    intro w hw
    obtain ⟨x, rfl⟩ := hmk w
    exact ⟨x, by rw [MonoidHom.mem_ker, ← hε]; exact hw, rfl⟩
  have hcen' : ε.ker ≤ Subgroup.center (G ⧸ C) := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hkermem w hw
    rw [Subgroup.mem_center_iff]
    intro v
    obtain ⟨y, rfl⟩ := hmk v
    have h1 : mk ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hcen x hx y)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hpow' : ∀ w ∈ ε.ker, ∃ n : ℕ, w ^ q ^ n = 1 := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hkermem w hw
    obtain ⟨n, hn⟩ := hpow x hx
    exact ⟨n, by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr hn⟩
  obtain ⟨P₁, hP₁, hP₁p⟩ := exists_perfect_cover ε (hrange hL₁) (perfect_of_quasisimple hqs₁)
  obtain ⟨P₂, hP₂, hP₂p⟩ := exists_perfect_cover ε (hrange hL₂) (perfect_of_quasisimple hqs₂)
  obtain ⟨P₃, hP₃, hP₃p⟩ := exists_perfect_cover ε (hrange hL₃) (perfect_of_quasisimple hqs₃)
  have hk₁ := cover_inf_ker_eq_bot ε hcen' hpow' hq hqs₁ hcl₁ hP₁p hP₁
  have hk₂ := cover_inf_ker_eq_bot ε hcen' hpow' hq hqs₂ hcl₂ hP₂p hP₂
  have hk₃ := cover_inf_ker_eq_bot ε hcen' hpow' hq hqs₃ hcl₃ hP₃p hP₃
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x₁, hx₁P, hx₁e⟩ : ∃ x ∈ P₁, ε x = t₁ := by
    have : t₁ ∈ P₁.map ε := hP₁ ▸ h₁
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp this
    exact ⟨x, hx, hxe⟩
  obtain ⟨x₂, hx₂P, hx₂e⟩ : ∃ x ∈ P₂, ε x = t₂ := by
    have : t₂ ∈ P₂.map ε := hP₂ ▸ h₂
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp this
    exact ⟨x, hx, hxe⟩
  obtain ⟨x₃, hx₃P, hx₃e⟩ : ∃ x ∈ P₃, ε x = t₃ := by
    have : t₃ ∈ P₃.map ε := hP₃ ▸ h₃
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp this
    exact ⟨x, hx, hxe⟩
  have hord : ∀ {P : Subgroup (G ⧸ C)} {x : G ⧸ C} {t : Y}, P ⊓ ε.ker = ⊥ → x ∈ P → ε x = t →
      orderOf t = q → orderOf x = q := by
    intro P x t hP hxP hxt ht
    have hxq : x ^ q = 1 := by
      have hmem : x ^ q ∈ P ⊓ ε.ker := Subgroup.mem_inf.mpr ⟨P.pow_mem hxP q,
        MonoidHom.mem_ker.mpr (by rw [map_pow, hxt, ← ht]; exact pow_orderOf_eq_one t)⟩
      rw [hP] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, map_one] at hxt
      rw [← hxt, orderOf_one] at ht
      exact hq.ne_one ht.symm
    exact orderOf_eq_prime hxq hx1
  have hmemL₁ : ∀ a ∈ P₁, ε a ∈ L₁ := fun a ha => hP₁ ▸ Subgroup.mem_map_of_mem ε ha
  have hmemL₂ : ∀ a ∈ P₂, ε a ∈ L₂ := fun a ha => hP₂ ▸ Subgroup.mem_map_of_mem ε ha
  have hmemL₃ : ∀ a ∈ P₃, ε a ∈ L₃ := fun a ha => hP₃ ▸ Subgroup.mem_map_of_mem ε ha
  have hc12 : x₁ * x₂ = x₂ * x₁ :=
    cover_commute ε hcen' hP₂p (fun a ha b hb => c12 _ (hmemL₁ a ha) _ (hmemL₂ b hb))
      x₁ hx₁P x₂ hx₂P
  have hc13 : x₁ * x₃ = x₃ * x₁ :=
    cover_commute ε hcen' hP₃p (fun a ha b hb => c13 _ (hmemL₁ a ha) _ (hmemL₃ b hb))
      x₁ hx₁P x₃ hx₃P
  have hc23 : x₂ * x₃ = x₃ * x₂ :=
    cover_commute ε hcen' hP₃p (fun a ha b hb => c23 _ (hmemL₂ a ha) _ (hmemL₃ b hb))
      x₂ hx₂P x₃ hx₃P
  have hnc₂ := qClean_exists_noncentral hq hqs₂ hcl₂ h₂ o₂
  have hnc₃ := qClean_exists_noncentral hq hqs₃ hcl₃ h₃ o₃
  have hb1 : x₂ ∉ Subgroup.closure {x₁} := by
    intro hmem
    have ht : t₂ ∈ Subgroup.closure {t₁} := by
      have := Subgroup.mem_map_of_mem ε hmem
      rw [MonoidHom.map_closure, Set.image_singleton, hx₂e, hx₁e] at this
      exact this
    obtain ⟨l, hl, hlt⟩ := hnc₂
    exact nf_notMem_closure (S := {t₁}) (fun s hs z hz => by
      rw [Set.mem_singleton_iff.mp hs]; exact c12 t₁ h₁ z hz) hl hlt ht
  have hc1 : x₃ ∉ Subgroup.closure {x₁, x₂} := by
    intro hmem
    have ht : t₃ ∈ Subgroup.closure {t₁, t₂} := by
      have := Subgroup.mem_map_of_mem ε hmem
      rw [MonoidHom.map_closure, Set.image_pair, hx₃e, hx₁e, hx₂e] at this
      exact this
    obtain ⟨l, hl, hlt⟩ := hnc₃
    refine nf_notMem_closure (S := {t₁, t₂}) ?_ hl hlt ht
    intro s hs z hz
    rcases Set.mem_insert_iff.mp hs with h | h
    · rw [h]; exact c13 t₁ h₁ z hz
    · rw [Set.mem_singleton_iff.mp h]; exact c23 t₂ h₂ z hz
  obtain ⟨hE, hcard⟩ := closure_three_elemAbelian hq hc12 hc13 hc23
    (hord hk₁ hx₁P hx₁e o₁) (hord hk₂ hx₂P hx₂e o₂) (hord hk₃ hx₃P hx₃e o₃) hb1 hc1
  exact exists_elemAbelian_lift hq C hCq _ hE hcard

theorem bn_conj_mem {X : Type} [Group X] (A : Subgroup X) (g : X)
    (hg : ∀ a : X, a ∈ A ↔ g * a * g⁻¹ ∈ A) (K : Subgroup ↥A) (hK : K.Characteristic)
    {k : ↥A} (hk : k ∈ K) : g * (k : X) * g⁻¹ ∈ K.map A.subtype := by
  have hinv : ∀ y : ↥A, g⁻¹ * (y : X) * g ∈ A := by
    intro y
    refine (hg (g⁻¹ * (y : X) * g)).mpr ?_
    rw [show g * (g⁻¹ * (y : X) * g) * g⁻¹ = (y : X) by group]
    exact y.2
  let φ : ↥A ≃* ↥A :=
    { toFun := fun x => ⟨g * (x : X) * g⁻¹, (hg (x : X)).mp x.2⟩
      invFun := fun y => ⟨g⁻¹ * (y : X) * g, hinv y⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hφk : φ k ∈ K := by
    have hk' : k ∈ K.comap φ.toMonoidHom := by
      rw [hK.fixed φ]
      exact hk
    exact hk'
  exact Subgroup.mem_map_of_mem A.subtype hφk

theorem exists_normal_q_complement {X : Type} [Group X] [Finite X] {q : ℕ} [Fact q.Prime]
    (J A R : Subgroup X) (hAJ : A ≤ J) (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A)
    (hRA : R ≤ A) (hRq : IsPGroup q R) (hRsyl : ¬ q ∣ R.relIndex A)
    (hRc : ∀ j ∈ J, ∀ r ∈ R, j * r = r * j) :
    ∃ C : Subgroup X, C ≤ A ∧ ¬ q ∣ Nat.card C ∧
      (∀ g : X, (∀ a : X, a ∈ A ↔ g * a * g⁻¹ ∈ A) → ∀ c ∈ C, g * c * g⁻¹ ∈ C) ∧
      (∀ a ∈ A, ∃ r ∈ R, ∃ c ∈ C, a = r * c) := by
  have hcen : ∀ x y : ↥A, y ∈ R.subgroupOf A → y * x = x * y := by
    intro x y hy
    apply Subtype.ext
    exact (hRc x.1 (hAJ x.2) y.1 (Subgroup.mem_subgroupOf.mp hy)).symm
  have hQq : IsPGroup q (R.subgroupOf A) := hRq.of_equiv (Subgroup.subgroupOfEquivOfLe hRA).symm
  have hQi : ¬ q ∣ (R.subgroupOf A).index := hRsyl
  obtain ⟨P, hPdef⟩ : ∃ P : Sylow q ↥A, (P : Subgroup ↥A) = R.subgroupOf A :=
    ⟨hQq.toSylow hQi, rfl⟩
  have hPn : Subgroup.normalizer (P : Set ↥A) ≤ Subgroup.centralizer (P : Set ↥A) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ R.subgroupOf A := by
      rw [← hPdef]
      exact hh
    exact hcen x h hh'
  obtain ⟨K, hKn, hKp, -, -, hKchar, -, hKsup, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hPn
  rw [hPdef] at hKsup
  refine ⟨K.map A.subtype, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact k.2
  · rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hKp
  · intro g hg c hc
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hc
    exact bn_conj_mem A g hg K hKchar hk
  · intro a ha
    have h1 : (⟨a, ha⟩ : ↥A) ∈ K ⊔ R.subgroupOf A := by
      rw [hKsup]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, y, hy, hky⟩ := Subgroup.mem_sup_of_normal_left.mp h1
    have h2 : y * k = ⟨a, ha⟩ := by
      rw [← hky]
      exact hcen k y hy
    exact ⟨y.1, Subgroup.mem_subgroupOf.mp hy, k.1, Subgroup.mem_map_of_mem A.subtype hk,
      (congrArg Subtype.val h2).symm⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

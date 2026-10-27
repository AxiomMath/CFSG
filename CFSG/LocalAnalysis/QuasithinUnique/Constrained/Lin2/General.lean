module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Helpers
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section TIConj

variable {G : Type*} [Group G]

theorem fusionIsTI_iff_conjR {U : Subgroup G} :
    fusionIsTI U ↔ ∀ g : G, conjR U g ≠ U → U ⊓ conjR U g = ⊥ := by
  have key : ∀ g : G, U.map (MulAut.conj g).toMonoidHom = conjR U g⁻¹ := by
    intro g
    rw [conjR_def, inv_inv]
  constructor
  · intro h g hg
    have := h g⁻¹ (by rw [key, inv_inv]; exact hg)
    rwa [key, inv_inv] at this
  · intro h g hg
    rw [key] at hg ⊢
    exact h g⁻¹ hg

theorem fusionIsTI_conjR {U : Subgroup G} (h : fusionIsTI U) (x : G) :
    fusionIsTI (conjR U x) := by
  rw [fusionIsTI_iff_conjR] at h ⊢
  intro g hg
  have hne : conjR U (x * g * x⁻¹) ≠ U := by
    intro he
    apply hg
    rw [conjR_conjR]
    have := congrArg (fun K => conjR K x) he
    simp only [conjR_conjR] at this
    simpa [mul_assoc] using this
  have := h _ hne
  have e : conjR U x ⊓ conjR (conjR U x) g = conjR (U ⊓ conjR U (x * g * x⁻¹)) x := by
    rw [conjR_inf, conjR_conjR, conjR_conjR]
    simp [mul_assoc]
  rw [e, this, conjR_bot]

theorem conjR_eq_of_inf_ne_bot {U : Subgroup G} (h : fusionIsTI U) {g : G}
    (hne : U ⊓ conjR U g ≠ ⊥) : conjR U g = U := by
  by_contra hg
  exact hne (fusionIsTI_iff_conjR.1 h g hg)

end TIConj

section Products

variable {G : Type*} [Group G]

theorem mem_sup_iff_of_le_normalizer {N H : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) {k : G} :
    k ∈ N ⊔ H ↔ ∃ n ∈ N, ∃ h ∈ H, k = n * h := by
  have := Subgroup.coe_mul_of_right_le_normalizer_left N H hLE
  rw [← SetLike.mem_coe, this]
  exact ⟨fun ⟨n, hn, h, hh, e⟩ => ⟨n, hn, h, hh, e.symm⟩,
    fun ⟨n, hn, h, hh, e⟩ => ⟨n, hn, h, hh, e.symm⟩⟩

theorem le_normalizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set G) :=
  le_normalizer_of_conj_mem fun b hb a ha => by
    have : b * a * b⁻¹ = a := by rw [← h a ha b hb]; group
    rw [this]; exact ha

theorem unique_decomp {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a a' b b' : G} (ha : a ∈ A)
    (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a ∈ A ⊓ B := by
    refine ⟨A.mul_mem (A.inv_mem ha') ha, ?_⟩
    have : a'⁻¹ * a = b' * b⁻¹ := by
      have : a = a' * b' * b⁻¹ := by rw [← h]; group
      rw [this]; group
    rw [this]
    exact B.mul_mem hb' (B.inv_mem hb)
  rw [hAB, Subgroup.mem_bot] at h1
  have e1 : a = a' := (inv_mul_eq_one.1 h1).symm
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact mul_left_cancel h

theorem mem_sup_zpowers_of_sq_eq_one {R : Subgroup G} {t : G}
    (hn : t ∈ Subgroup.normalizer (R : Set G)) (ht : t ^ 2 = 1) {k : G}
    (hk : k ∈ R ⊔ Subgroup.zpowers t) : k ∈ R ∨ ∃ r ∈ R, k = r * t := by
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.2 hn
  obtain ⟨r, hr, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer hle).1 hk
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  rcases zpow_of_sq_eq_one ht j with h | h
  · left; rw [h, mul_one]; exact hr
  · right; exact ⟨r, hr, by rw [h]⟩

theorem card_le_two_of_forall {A N : Subgroup G}
    (h : ∀ a ∈ A, a ∉ N → ∀ b ∈ A, b ∉ N → a⁻¹ * b ∈ N) (hbot : A ⊓ N = ⊥) :
    Nat.card A ≤ 2 := by
  classical
  have hinj : Function.Injective (fun a : A => decide ((a : G) ∈ N)) := by
    intro a b hab
    simp only [decide_eq_decide] at hab
    by_cases ha : (a : G) ∈ N
    · have hb : (b : G) ∈ N := hab.1 ha
      have h1 : (a : G) ∈ A ⊓ N := ⟨a.2, ha⟩
      have h2 : (b : G) ∈ A ⊓ N := ⟨b.2, hb⟩
      rw [hbot, Subgroup.mem_bot] at h1 h2
      exact Subtype.ext (h1.trans h2.symm)
    · have hb : (b : G) ∉ N := fun hb => ha (hab.2 hb)
      have h1 := h a a.2 ha b b.2 hb
      have h2 : (a : G)⁻¹ * b ∈ A ⊓ N := ⟨A.mul_mem (A.inv_mem a.2) b.2, h1⟩
      rw [hbot, Subgroup.mem_bot] at h2
      exact Subtype.ext (inv_mul_eq_one.1 h2)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem actsRegularlyOn_sup_of_prod {D D' Z Z' : Subgroup G}
    (hcommD : ∀ d ∈ D, ∀ d' ∈ D', d * d' = d' * d)
    (hZZ' : Z ⊓ Z' = ⊥) (hcommZ : ∀ z ∈ Z, ∀ z' ∈ Z', z * z' = z' * z)
    (hDZ : ∀ d ∈ D, ∀ z ∈ Z, d⁻¹ * z * d = z) (hD'Z' : ∀ d' ∈ D', ∀ z' ∈ Z', d'⁻¹ * z' * d' = z')
    (hD : ActsRegularlyOn D (nonIdentity Z')) (hD' : ActsRegularlyOn D' (nonIdentity Z)) :
    ActsRegularlyOn (D ⊔ D') {u | u ∈ Z ⊔ Z' ∧ u ∉ Z ∧ u ∉ Z'} := by
  have hN1 : ∀ d' ∈ D', ∀ z ∈ Z, d'⁻¹ * z * d' ∈ Z := by
    intro d' hd' z hz
    by_cases hz1 : z = 1
    · subst hz1; simp
    · exact (hD'.1 d' hd' z ⟨hz, hz1⟩).1
  have hN2 : ∀ d ∈ D, ∀ z' ∈ Z', d⁻¹ * z' * d ∈ Z' := by
    intro d hd z' hz'
    by_cases hz1 : z' = 1
    · subst hz1; simp
    · exact (hD.1 d hd z' ⟨hz', hz1⟩).1
  have hDN : D ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_of_conj_mem fun d hd z hz => by
    have h := hDZ d⁻¹ (D.inv_mem hd) z hz
    rw [inv_inv] at h
    rw [h]; exact hz
  have hDN' : D ≤ Subgroup.normalizer (Z' : Set G) := le_normalizer_of_conj_mem fun d hd z hz => by
    have := hN2 d⁻¹ (D.inv_mem hd) z hz
    simpa using this
  have hD'N : D' ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_of_conj_mem fun d hd z hz => by
    have := hN1 d⁻¹ (D'.inv_mem hd) z hz
    simpa using this
  have hD'N' : D' ≤ Subgroup.normalizer (Z' : Set G) := le_normalizer_of_conj_mem fun d hd z hz => by
    have h := hD'Z' d⁻¹ (D'.inv_mem hd) z hz
    rw [inv_inv] at h
    rw [h]; exact hz
  have hD'D : D' ≤ Subgroup.normalizer (D : Set G) := le_normalizer_of_commute hcommD
  have hZ'Z : Z' ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_of_commute hcommZ
  have hBN : D ⊔ D' ≤ Subgroup.normalizer ((Z ⊔ Z' : Subgroup G) : Set G) := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (Z : Set G) ⊓ Subgroup.normalizer (Z' : Set G) := by
      have : D ⊔ D' ≤ Subgroup.normalizer (Z : Set G) ⊓ Subgroup.normalizer (Z' : Set G) :=
        sup_le (le_inf hDN hDN') (le_inf hD'N hD'N')
      exact this hb
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ hbN
  have hBNZ : D ⊔ D' ≤ Subgroup.normalizer (Z : Set G) := sup_le hDN hD'N
  have hBNZ' : D ⊔ D' ≤ Subgroup.normalizer (Z' : Set G) := sup_le hDN' hD'N'
  have hdecW : ∀ w ∈ Z ⊔ Z', ∃ z ∈ Z, ∃ z' ∈ Z', w = z * z' := fun w hw =>
    (mem_sup_iff_of_le_normalizer hZ'Z).1 hw
  have hact : ∀ d ∈ D, ∀ d' ∈ D', ∀ z ∈ Z, ∀ z' ∈ Z',
      (d * d')⁻¹ * (z * z') * (d * d') = (d'⁻¹ * z * d') * (d⁻¹ * z' * d) := by
    intro d hd d' hd' z hz z' hz'
    have e1 : (d * d')⁻¹ * (z * z') * (d * d') = d'⁻¹ * ((d⁻¹ * z * d) * (d⁻¹ * z' * d)) * d' := by
      group
    rw [e1, hDZ d hd z hz]
    have e2 : d'⁻¹ * (z * (d⁻¹ * z' * d)) * d' =
        (d'⁻¹ * z * d') * (d'⁻¹ * (d⁻¹ * z' * d) * d') := by
      group
    rw [e2, hD'Z' d' hd' _ (hN2 d hd z' hz')]
  refine ⟨?_, ?_, ?_⟩
  · rintro b hb u ⟨huW, huZ, huZ'⟩
    have hb' : b⁻¹ ∈ D ⊔ D' := (D ⊔ D').inv_mem hb
    refine ⟨?_, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (hBN hb') u).1 huW
      simpa using this
    · intro h
      apply huZ
      have := (Subgroup.mem_normalizer_iff.1 (hBNZ hb) (b⁻¹ * u * b)).1 h
      simpa [mul_assoc] using this
    · intro h
      apply huZ'
      have := (Subgroup.mem_normalizer_iff.1 (hBNZ' hb) (b⁻¹ * u * b)).1 h
      simpa [mul_assoc] using this
  · rintro u₁ ⟨hu₁W, hu₁Z, hu₁Z'⟩ u₂ ⟨hu₂W, hu₂Z, hu₂Z'⟩
    obtain ⟨z₁, hz₁, z₁', hz₁', rfl⟩ := hdecW u₁ hu₁W
    obtain ⟨z₂, hz₂, z₂', hz₂', rfl⟩ := hdecW u₂ hu₂W
    have hz₁1 : z₁ ≠ 1 := by
      rintro rfl; apply hu₁Z'; simpa using hz₁'
    have hz₁'1 : z₁' ≠ 1 := by
      rintro rfl; apply hu₁Z; simpa using hz₁
    have hz₂1 : z₂ ≠ 1 := by
      rintro rfl; apply hu₂Z'; simpa using hz₂'
    have hz₂'1 : z₂' ≠ 1 := by
      rintro rfl; apply hu₂Z; simpa using hz₂
    obtain ⟨d, hd, hdz⟩ := hD.2.1 z₁' ⟨hz₁', hz₁'1⟩ z₂' ⟨hz₂', hz₂'1⟩
    obtain ⟨d', hd', hd'z⟩ := hD'.2.1 z₁ ⟨hz₁, hz₁1⟩ z₂ ⟨hz₂, hz₂1⟩
    refine ⟨d * d', Subgroup.mul_mem_sup hd hd', ?_⟩
    rw [hact d hd d' hd' z₁ hz₁ z₁' hz₁', hdz, hd'z]
  · rintro u ⟨huW, huZ, huZ'⟩ b hb hbu
    obtain ⟨z, hz, z', hz', rfl⟩ := hdecW u huW
    have hz1 : z ≠ 1 := by
      rintro rfl; apply huZ'; simpa using hz'
    have hz'1 : z' ≠ 1 := by
      rintro rfl; apply huZ; simpa using hz
    obtain ⟨d, hd, d', hd', rfl⟩ := (mem_sup_iff_of_le_normalizer hD'D).1 hb
    rw [hact d hd d' hd' z hz z' hz'] at hbu
    have hz1' : d'⁻¹ * z * d' ∈ Z := hN1 d' hd' z hz
    have hz2' : d⁻¹ * z' * d ∈ Z' := hN2 d hd z' hz'
    obtain ⟨e1, e2⟩ := unique_decomp hZZ' hz1' hz hz2' hz' hbu
    have h1 := hD'.2.2 z ⟨hz, hz1⟩ d' hd' e1
    have h2 := hD.2.2 z' ⟨hz', hz'1⟩ d hd e2
    rw [h1, h2, mul_one]

end Products

section WeakClosure

variable {G : Type*} [Group G]

theorem weakClosure_mono {A T T' : Subgroup G} (h : T ≤ T') :
    weakClosure A T ≤ weakClosure A T' :=
  iSup₂_le fun g hg => le_iSup₂_of_le g (hg.trans h) le_rfl

theorem le_weakClosure {A T : Subgroup G} {g : G} (h : conjR A g ≤ T) :
    conjR A g ≤ weakClosure A T :=
  le_iSup₂_of_le g h le_rfl

theorem weakClosure_le {A T : Subgroup G} : weakClosure A T ≤ T := iSup₂_le fun _ hg => hg

theorem conjR_weakClosure (A X : Subgroup G) (x : G) :
    conjR (weakClosure A X) x = weakClosure A (conjR X x) := by
  apply le_antisymm
  · rw [conjR_def, weakClosure, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    have : (conjR A g).map (MulAut.conj x⁻¹).toMonoidHom = conjR (conjR A g) x := rfl
    rw [this, conjR_conjR]
    exact le_weakClosure (by rw [← conjR_conjR]; exact conjR_mono hg x)
  · refine iSup₂_le fun g hg => ?_
    have h1 : conjR A (g * x⁻¹) ≤ X := by
      have := conjR_mono hg x⁻¹
      rwa [conjR_conjR, conjR_conjR, mul_inv_cancel, conjR_one] at this
    have h2 := conjR_mono (le_weakClosure h1) x
    rwa [conjR_conjR, inv_mul_cancel_right] at h2

end WeakClosure

section Regular

variable {G : Type*} [Group G]

theorem mem_nonIdentity_conjR {A : Subgroup G} {g z : G} :
    z ∈ nonIdentity (conjR A g) ↔ g * z * g⁻¹ ∈ nonIdentity A := by
  show (z ∈ conjR A g ∧ z ≠ 1) ↔ (g * z * g⁻¹ ∈ A ∧ g * z * g⁻¹ ≠ 1)
  rw [mem_conjR, Ne, Ne, conj_eq_one_iff]

theorem actsRegularlyOn_conjR {B A : Subgroup G} (h : ActsRegularlyOn B (nonIdentity A)) (g : G) :
    ActsRegularlyOn (conjR B g) (nonIdentity (conjR A g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro b hb z hz
    rw [mem_conjR] at hb
    rw [mem_nonIdentity_conjR] at hz ⊢
    have := h1 _ hb _ hz
    have e : g * (b⁻¹ * z * b) * g⁻¹ = (g * b * g⁻¹)⁻¹ * (g * z * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]; exact this
  · intro z hz z' hz'
    rw [mem_nonIdentity_conjR] at hz hz'
    obtain ⟨b, hb, hbz⟩ := h2 _ hz _ hz'
    refine ⟨g⁻¹ * b * g, ?_, ?_⟩
    · rw [mem_conjR]
      have : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      rw [this]; exact hb
    · have e : g * ((g⁻¹ * b * g)⁻¹ * z * (g⁻¹ * b * g)) * g⁻¹ = g * z' * g⁻¹ := by
        rw [← hbz]; group
      have := mul_right_cancel e
      exact mul_left_cancel this
  · intro z hz b hb hbz
    rw [mem_conjR] at hb
    rw [mem_nonIdentity_conjR] at hz
    have e : (g * b * g⁻¹)⁻¹ * (g * z * g⁻¹) * (g * b * g⁻¹) = g * z * g⁻¹ := by
      calc _ = g * (b⁻¹ * z * b) * g⁻¹ := by group
        _ = g * z * g⁻¹ := by rw [hbz]
    have := h3 _ hz _ hb e
    exact (conj_eq_one_iff.1 this)

theorem conjR_centralizes {D Z : Subgroup G} (h : ∀ d ∈ D, ∀ z ∈ Z, d⁻¹ * z * d = z) (x : G) :
    ∀ d' ∈ conjR D x, ∀ z' ∈ conjR Z x, d'⁻¹ * z' * d' = z' := by
  intro d' hd' z' hz'
  rw [mem_conjR] at hd' hz'
  have := h _ hd' _ hz'
  have e : x * (d'⁻¹ * z' * d') * x⁻¹ =
      (x * d' * x⁻¹)⁻¹ * (x * z' * x⁻¹) * (x * d' * x⁻¹) := by group
  rw [← e] at this
  exact mul_left_cancel (mul_right_cancel this)

end Regular

section Orders2

variable {G : Type*} [Group G]

theorem card_eq_mul_of_relIndex {S T : Subgroup G} (hST : S ≤ T) :
    Nat.card T = Nat.card S * S.relIndex T := by
  have := Subgroup.card_mul_index (S.subgroupOf T)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv] at this
  exact this.symm

theorem centralizer_le_normalizer_of_TI {Z : Subgroup G} (hTI : fusionIsTI Z) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  rw [← conjR_eq_self_iff]
  apply conjR_eq_of_inf_ne_bot hTI
  intro hbot
  have hmem : z ∈ Z ⊓ conjR Z g := by
    refine ⟨hz, mem_conjR.2 ?_⟩
    have : g * z * g⁻¹ = z := by rw [hg]; group
    rw [this]; exact hz
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 hmem

end Orders2

section DeltaCentral

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_lin2Delta_center {R Z T : Subgroup G} {x : G} (hT : IsPGroup 2 T)
    (hRT : R ≤ T) (hZR : Z ≤ centerOf R) (hZne : Z ≠ ⊥) (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hx : x ∈ T)
    (hnc : ∀ z ∈ Z, z ≠ 1 → ¬ T ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ u ∈ lin2Delta R Z x, u ∈ centerOf T := by
  have hcR : centerOf R ≤ T := inf_le_left.trans hRT
  have hn : T ≤ Subgroup.normalizer ((centerOf R : Subgroup G) : Set G) := fun g hg => by
    rw [← conjR_eq_self_iff]; exact centerOf_normalized (hTR hg)
  have hne : centerOf R ≠ ⊥ := fun h => hZne (le_bot_iff.1 (h ▸ hZR))
  obtain ⟨w, hw, hw1, hwT⟩ := exists_mem_inf_center_of_normal hT hcR hn hne
  refine ⟨w, ⟨hw, ?_, ?_⟩, ⟨hcR hw, hwT⟩⟩
  · intro hwZ
    refine hnc w hwZ hw1 fun t ht => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hwT t ht
  · intro hwZ
    rw [mem_conjR] at hwZ
    have : x * w * x⁻¹ = w := by
      have := Subgroup.mem_centralizer_iff.1 hwT x hx
      rw [this]; group
    rw [this] at hwZ
    refine hnc w hwZ hw1 fun t ht => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hwT t ht

end DeltaCentral

section SylowConj

variable {G : Type*} [Group G] [Finite G]

theorem exists_le_conjR_of_isSylowTwoOf {S N P : Subgroup G} (hS : IsSylowTwoOf S N)
    (hPN : P ≤ N) (hP : IsPGroup 2 P) : ∃ g ∈ N, P ≤ conjR S g := by
  obtain ⟨S', hPS', hS'⟩ := exists_isSylowTwoOf_of_le hPN hP
  obtain ⟨h, hh, hS'eq⟩ := hS.exists_conj hS'
  refine ⟨h⁻¹, N.inv_mem hh, ?_⟩
  rw [conjR_def, inv_inv, ← hS'eq]
  exact hPS'

end SylowConj

section Small

variable {G : Type*} [Group G]

theorem exists_mem_ne_two {Z : Subgroup G} (h : 2 < Nat.card Z) (z : G) :
    ∃ a ∈ Z, a ≠ 1 ∧ a ≠ z := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun a : Z => decide ((a : G) = 1)) := by
    intro a b hab
    simp only [decide_eq_decide] at hab
    by_cases ha : (a : G) = 1
    · have hb : (b : G) = 1 := hab.1 ha
      exact Subtype.ext (ha.trans hb.symm)
    · have hb : (b : G) ≠ 1 := fun hb => ha (hab.2 hb)
      exact Subtype.ext ((hcon a a.2 ha).trans (hcon b b.2 hb).symm)
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem le_of_mem_sdiff {A B P : Subgroup G} (hAB : A ⊓ B = ⊥) (hA : 2 < Nat.card A)
    (hB : B ≠ ⊥) (hP : ∀ u, u ∈ A ⊔ B → u ∉ A → u ∉ B → u ∈ P) : A ≤ P := by
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]; exact one_mem P
  obtain ⟨a₂, ha₂, ha₂1, ha₂'⟩ := exists_mem_ne_two hA a⁻¹
  obtain ⟨⟨b, hb⟩, hb1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
  have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
  have key : ∀ c ∈ A, c ≠ 1 → c * b ∈ P := by
    intro c hc hc1
    refine hP _ (Subgroup.mul_mem_sup hc hb) ?_ ?_
    · intro hcb
      have h1 : b ∈ A := by
        have := A.mul_mem (A.inv_mem hc) hcb
        simpa using this
      have h2 : b ∈ A ⊓ B := ⟨h1, hb⟩
      rw [hAB, Subgroup.mem_bot] at h2
      exact hb1 h2
    · intro hcb
      have h1 : c ∈ B := by
        have := B.mul_mem hcb (B.inv_mem hb)
        simpa using this
      have h2 : c ∈ A ⊓ B := ⟨hc, h1⟩
      rw [hAB, Subgroup.mem_bot] at h2
      exact hc1 h2
  have h1 : a * a₂ ≠ 1 := fun h => ha₂' (eq_inv_of_mul_eq_one_right h)
  have e : a = ((a * a₂) * b) * (a₂ * b)⁻¹ := by group
  rw [e]
  exact P.mul_mem (key _ (A.mul_mem ha ha₂) h1) (P.inv_mem (key _ ha₂ ha₂1))

theorem isElemAbelian_zpowers_of_sq_eq_one {z : G} (hz : z ^ 2 = 1) :
    IsElemAbelian 2 (Subgroup.zpowers z) := CFSG.Open.isElemAbelian_zpowers hz

end Small

end CFSG.QuasithinUnique.Lin2

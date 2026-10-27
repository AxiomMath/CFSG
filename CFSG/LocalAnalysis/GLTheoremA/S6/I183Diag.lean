module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs62
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification
  CFSG.HardMathSupport.Solomon.Coordinator Subgroup
open scoped Pointwise commutatorElement

section Helpers

variable {G : Type} [Group G]

theorem idiag_index_dichotomy {p : ℕ} (hp : p.Prime) {A S D : Subgroup G}
    (hidx : A.relIndex D = p) (hAS : A ≤ S) (hSD : S ≤ D) : S = A ∨ S = D := by
  have h := Subgroup.relIndex_mul_relIndex A S D hAS hSD
  rw [hidx] at h
  rcases Nat.prime_mul_iff.1 (h ▸ hp) with ⟨_, h2⟩ | ⟨_, h1⟩
  · right
    exact le_antisymm hSD (Subgroup.relIndex_eq_one.1 h2)
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hAS

theorem idiag_commute {p : ℕ} {D : Subgroup G} (hD : IsElemAbelian p D) {x y : G} (hx : x ∈ D)
    (hy : y ∈ D) : Commute x y := by
  have h := hD.1.is_comm.comm (⟨x, hx⟩ : ↥D) ⟨y, hy⟩
  exact congrArg Subtype.val h

theorem idiag_zpow_nat {p : ℕ} (hp : 0 < p) {d : G} (hdp : d ^ p = 1) (k : ℤ) :
    ∃ n : ℕ, d ^ k = d ^ n := by
  have hpz : d ^ (p : ℤ) = 1 := by rwa [zpow_natCast]
  refine ⟨(k % (p : ℤ)).toNat, ?_⟩
  have h0 : 0 ≤ k % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  rw [zpow_eq_zpow_emod k hpz, ← zpow_natCast, Int.toNat_of_nonneg h0]

theorem idiag_decomp {p : ℕ} (hp : p.Prime) {A D : Subgroup G} (hD : IsElemAbelian p D)
    (hAD : A ≤ D) (hidx : A.relIndex D = p) {d : G} (hd : d ∈ D) (hdA : d ∉ A) :
    ∀ e ∈ D, ∃ a ∈ A, ∃ k : ℕ, e = a * d ^ k := by
  have hdp : d ^ p = 1 := hD.2 d hd
  let T : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ k : ℤ, x = a * d ^ k}
      one_mem' := ⟨1, A.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, k, rfl⟩ ⟨b, hb, l, rfl⟩
        have hc : Commute (d ^ k) b :=
          idiag_commute hD (D.zpow_mem hd k) (hAD hb)
        refine ⟨a * b, A.mul_mem ha hb, k + l, ?_⟩
        calc a * d ^ k * (b * d ^ l) = a * (d ^ k * b) * d ^ l := by group
          _ = a * (b * d ^ k) * d ^ l := by rw [hc.eq]
          _ = a * b * d ^ (k + l) := by rw [zpow_add]; group
      inv_mem' := by
        rintro _ ⟨a, ha, k, rfl⟩
        have hc : Commute a (d ^ k) :=
          (idiag_commute hD (hAD ha) (D.zpow_mem hd k))
        refine ⟨a⁻¹, A.inv_mem ha, -k, ?_⟩
        rw [zpow_neg]
        calc (a * d ^ k)⁻¹ = (d ^ k)⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * (d ^ k)⁻¹ := (hc.inv_inv.eq).symm }
  have hsub : A ⊔ zpowers d ≤ T := by
    refine sup_le (fun a ha => ⟨a, ha, 0, by simp⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨1, A.one_mem, 1, by simp⟩
  have hSD : A ⊔ zpowers d ≤ D :=
    sup_le hAD (Subgroup.zpowers_le.2 hd)
  have htop : A ⊔ zpowers d = D := by
    rcases idiag_index_dichotomy hp hidx le_sup_left hSD with h | h
    · have hd' : d ∈ A ⊔ zpowers d := (le_sup_right : zpowers d ≤ A ⊔ zpowers d) (Subgroup.mem_zpowers d)
      rw [h] at hd'
      exact absurd hd' hdA
    · exact h
  intro e he
  have heT : e ∈ T := by
    have : D ≤ A ⊔ zpowers d := htop.ge
    exact hsub (this he)
  obtain ⟨a, ha, k, rfl⟩ := heT
  obtain ⟨n, hn⟩ := idiag_zpow_nat hp.pos hdp k
  exact ⟨a, ha, n, by rw [hn]⟩

theorem idiag_gLBConj_eq_of_comm {g : G} {H : Subgroup G} (h : ∀ y ∈ H, g * y = y * g) :
    GLBConj g H = H := by
  ext z
  rw [mem_gLBConj]
  constructor
  · intro hz
    have hc := h _ hz
    have key : z = g * z * g⁻¹ := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * z * g⁻¹)) := by rw [hc]
        _ = g * z * g⁻¹ := by group
    rw [← key] at hz
    exact hz
  · intro hz
    have := h z hz
    rw [this]
    simpa using hz

theorem idiag_stab {p : ℕ} (hp : p.Prime) {A D X C : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hAD : A ≤ D) (hidx : A.relIndex D = p) (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a)
    (hCX : C ≤ X) (hC : C ∈ 𝒞) (hne : ∃ C₂ ∈ 𝒞, C₂ ≠ C)
    (htrans : ∀ C' ∈ 𝒞, ∀ C'' ∈ 𝒞, ∃ e ∈ D, GLBConj e C' = C'')
    {e : G} (he : e ∈ D) (hfix : GLBConj e C = C) : e ∈ A := by
  classical
  let S : Subgroup G := D ⊓ Subgroup.normalizer (C : Set G)
  have hAS : A ≤ S := by
    intro a ha
    refine ⟨hAD ha, ?_⟩
    exact mem_normalizer_iff_gLBConj_eq.2 (idiag_gLBConj_eq_of_comm (fun y hy => hAX a ha y (hCX hy)))
  have hSD : S ≤ D := inf_le_left
  have hSne : S ≠ D := by
    intro hS
    obtain ⟨C₂, hC₂, hne₂⟩ := hne
    obtain ⟨e₂, he₂, hC₂e⟩ := htrans C hC C₂ hC₂
    have he₂S : e₂ ∈ S := hS ▸ he₂
    have h1 : GLBConj e₂ C = C := mem_normalizer_iff_gLBConj_eq.1 he₂S.2
    exact hne₂ (hC₂e.symm.trans h1)
  rcases idiag_index_dichotomy hp hidx hAS hSD with h | h
  · have heS : e ∈ S := ⟨he, mem_normalizer_iff_gLBConj_eq.2 hfix⟩
    rw [h] at heS
    exact heS
  · exact absurd h hSne

theorem idiag_zcap {p : ℕ} (hp : p.Prime) {A D : Subgroup G} (hD : IsElemAbelian p D)
    {d : G} (hd : d ∈ D) (hdA : d ∉ A) {z : G} (hz : z ∈ Subgroup.zpowers d) (hzA : z ∈ A) :
    z = 1 := by
  have hdp : d ^ p = 1 := hD.2 d hd
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, z = d ^ n := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    obtain ⟨n, hn⟩ := idiag_zpow_nat hp.pos hdp k
    exact ⟨n, by rw [← hk, hn]⟩
  by_contra hz1
  have hpn : ¬ p ∣ n := by
    rintro ⟨q, rfl⟩
    apply hz1
    rw [pow_mul, hdp, one_pow]
  have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hzm : (d ^ n) ^ m = d := by
    rw [← pow_mul]
    have h1 := Nat.div_add_mod (n * m) p
    rw [hm] at h1
    rw [← h1, pow_add, pow_mul, hdp, one_pow, one_mul, pow_one]
  apply hdA
  rw [← hzm]
  exact A.pow_mem hzA m

end Helpers


section Family

variable {G : Type} [Group G] [Finite G]

theorem idiag_barX_ne {p : ℕ} {X C₁ C₂ : Subgroup G} (h₁ : GLAPComponent p X C₁)
    (h₂ : GLAPComponent p X C₂) (hne : C₁ ≠ C₂) : barX p X C₁ ≠ barX p X C₂ :=
  fun h => hne (glaPComponent_unique h₁ h₂ h)

theorem idiag_barX_commute {p : ℕ} {X C₁ C₂ : Subgroup G} (h₁ : GLAPComponent p X C₁)
    (h₂ : GLAPComponent p X C₂) (hne : C₁ ≠ C₂) : ⁅barX p X C₁, barX p X C₂⁆ = ⊥ :=
  LocalComponents.commute_of_ne _ _ h₁.2.2.1 h₂.2.2.1 (idiag_barX_ne h₁ h₂ hne)

theorem idiag_barX_isComponent {p : ℕ} {X : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) {C : Subgroup G} (hC : C ∈ 𝒞) :
    IsComponentOf (barX p X C) (⨆ C' : 𝒞, barX p X (C' : Subgroup G)) := by
  have hle : barX p X C ≤ ⨆ C' : 𝒞, barX p X (C' : Subgroup G) :=
    le_iSup (fun C' : 𝒞 => barX p X (C' : Subgroup G)) ⟨C, hC⟩
  have hN : (⨆ C' : 𝒞, barX p X (C' : Subgroup G)) ≤
      Subgroup.normalizer (barX p X C : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    refine iSup_le fun C' => ?_
    by_cases h : (C' : Subgroup G) = C
    · rw [h]
      exact Subgroup.le_normalizer
    · have hc := idiag_barX_commute (hcomp _ C'.2) (hcomp C hC) h
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc).trans
        (Subgroup.centralizer_le_normalizer _)
  have hsub : IsSubnormal (barX p X C) (⨆ C' : 𝒞, barX p X (C' : Subgroup G)) :=
    CFSG.Quasithin.A3.subnormal_of_normal hle (by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
      exact hN)
  exact ⟨hle, hsub, (hcomp C hC).2.2.1.2.2⟩

theorem idiag_component_eq {p : ℕ} {X : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C)
    {L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)}
    (hL : IsComponentOf L (⨆ C' : 𝒞, barX p X (C' : Subgroup G))) :
    ∃ C ∈ 𝒞, barX p X C = L := by
  classical
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ C' : 𝒞, ∀ x ∈ L, ∀ y ∈ barX p X (C' : Subgroup G), Commute x y := by
    intro C' x hx y hy
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hL
        (idiag_barX_isComponent hcomp C'.2) with h | h
    · exact absurd h.symm (hcon _ C'.2)
    · exact h x hx y hy
  have hcentral : ∀ x ∈ L, ∀ y ∈ (⨆ C' : 𝒞, barX p X (C' : Subgroup G)), Commute x y := by
    intro x hx y hy
    refine Subgroup.iSup_induction (fun C' : 𝒞 => barX p X (C' : Subgroup G)) (C := fun y => Commute x y)
      hy (fun C' y hy => hcomm C' x hx y hy) (Commute.one_right x) (fun a b ha hb => ha.mul_right hb)
  have hLcomm : ⁅L, L⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hc : Commute g₁ g₂ := hcentral g₁ hg₁ g₂ (hL.1 hg₂)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact hc
  have hperf := i25_commutator_eq hL.2.2
  rw [hLcomm] at hperf
  exact (Subgroup.nontrivial_iff_ne_bot _).1 (Quasisimple.nontrivial hL.2.2) hperf.symm

end Family

section Cyclic

variable {G : Type} [Group G] [Finite G]

theorem idiag_gLBConj_iSup {Y : Type*} [Group Y] {ι : Sort*} (g : Y) (S : ι → Subgroup Y) :
    GLBConj g (⨆ i, S i) = ⨆ i, GLBConj g (S i) :=
  Subgroup.map_iSup (MulAut.conj g⁻¹).toMonoidHom S

theorem idiag_conj_le {p : ℕ} {D X : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hinv : ∀ C ∈ 𝒞, ∀ e ∈ D, GLBConj e C ∈ 𝒞) {g : G} (hgD : g ∈ D) (hgX : g ∈ X) :
    GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩)
        (⨆ C' : 𝒞, barX p X (C' : Subgroup G)) ≤
      ⨆ C' : 𝒞, barX p X (C' : Subgroup G) := by
  rw [idiag_gLBConj_iSup]
  refine iSup_le fun C' => ?_
  rw [← i183v_barX_gLBConj (p := p) hgX (C' : Subgroup G)]
  exact le_iSup (fun C'' : 𝒞 => barX p X (C'' : Subgroup G)) ⟨GLBConj g C', hinv _ C'.2 g hgD⟩

theorem idiag_E_le_normalizer {p : ℕ} {D X : Subgroup G} {𝒞 : Set (Subgroup G)} {d : G}
    (hinv : ∀ C ∈ 𝒞, ∀ e ∈ D, GLBConj e C ∈ 𝒞) (hd : d ∈ D) (hdX : d ∈ X) :
    barX p X (Subgroup.zpowers d) ≤
      Subgroup.normalizer ((⨆ C' : 𝒞, barX p X (C' : Subgroup G) :
        Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  set Kb : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := ⨆ C' : 𝒞, barX p X (C' : Subgroup G) with hKb
  set eb : ↥X ⧸ GLAPPrimeCore p ↥X := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d, hdX⟩ with heb
  have hinv' : d⁻¹ ∈ D := D.inv_mem hd
  have hdX' : d⁻¹ ∈ X := X.inv_mem hdX
  have h1 : GLBConj eb Kb ≤ Kb := idiag_conj_le hinv hd hdX
  have h2 : GLBConj eb⁻¹ Kb ≤ Kb := by
    have e : eb⁻¹ = QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d⁻¹, hdX'⟩ := by
      rw [heb, ← map_inv]
      rfl
    rw [e]
    exact idiag_conj_le hinv hinv' hdX'
  have h3 : Kb ≤ GLBConj eb Kb := by
    have := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono eb h2
    rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at this
  have hmem : eb ∈ Subgroup.normalizer (Kb : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    mem_normalizer_iff_gLBConj_eq.2 (le_antisymm h1 h3)
  have hz : Subgroup.zpowers eb ≤ Subgroup.normalizer (Kb : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    Subgroup.zpowers_le.2 hmem
  intro e he
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 he
  have hxd : (x : G) ∈ Subgroup.zpowers d := (Subgroup.mem_subgroupOf).1 hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxd
  have hxe : QuotientGroup.mk' (GLAPPrimeCore p ↥X) x = eb ^ k := by
    rw [heb, ← map_zpow]
    congr 1
    exact Subtype.ext (by simp [← hk])
  rw [hxe]
  exact hz (Subgroup.zpow_mem _ (Subgroup.mem_zpowers eb) k)

end Cyclic

section Action

variable {G : Type} [Group G] [Finite G]

theorem idiag_elemAbelian_zpowers {p : ℕ} {d : G} (hdp : d ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers d) := by
  refine ⟨inferInstance, fun x hx => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]

theorem idiag_trans {p : ℕ} {A D X : Subgroup G} {𝒞 : Set (Subgroup G)} {d : G}
    (hp : p.Prime) (hD : IsElemAbelian p D) (hAD : A ≤ D) (hidx : A.relIndex D = p)
    (hd : d ∈ D) (hdA : d ∉ A) (hdX : d ∈ X) (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a)
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C)
    (htrans : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ D, GLBConj e C = C')
    {L L' : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)}
    (hL : IsComponentOf L (⨆ C' : 𝒞, barX p X (C' : Subgroup G)))
    (hL' : IsComponentOf L' (⨆ C' : 𝒞, barX p X (C' : Subgroup G))) :
    ∃ e ∈ barX p X (Subgroup.zpowers d), GLBConj e L = L' := by
  obtain ⟨C, hC, rfl⟩ := idiag_component_eq hcomp hL
  obtain ⟨C', hC', rfl⟩ := idiag_component_eq hcomp hL'
  obtain ⟨e', he', hCe⟩ := htrans C hC C' hC'
  obtain ⟨a, ha, k, rfl⟩ := idiag_decomp hp hD hAD hidx hd hdA e' he'
  have hCX : C ≤ X := (hcomp C hC).1
  have hfix : GLBConj a C = C := idiag_gLBConj_eq_of_comm (fun y hy => hAX a ha y (hCX hy))
  have hdkX : d ^ k ∈ X := X.pow_mem hdX k
  have hC'eq : GLBConj (d ^ k) C = C' := by
    have h1 := CFSG.LocalAnalysis.GLTheoremB.gLBConj_gLBConj (d ^ k) a C
    rw [hfix] at h1
    rw [h1]
    exact hCe
  refine ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d ^ k, hdkX⟩, ?_, ?_⟩
  · exact Subgroup.mem_map.2 ⟨⟨d ^ k, hdkX⟩,
      (Subgroup.mem_subgroupOf).2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) k), rfl⟩
  · rw [← hC'eq, i183v_barX_gLBConj hdkX C]

theorem idiag_free {p : ℕ} {A D X : Subgroup G} {𝒞 : Set (Subgroup G)} {d : G}
    (hp : p.Prime) (hD : IsElemAbelian p D) (hAD : A ≤ D) (hidx : A.relIndex D = p)
    (hd : d ∈ D) (hdA : d ∉ A) (hdX : d ∈ X) (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a)
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hne : ∀ C ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₂ ≠ C)
    (htrans : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ D, GLBConj e C = C')
    {e : ↥X ⧸ GLAPPrimeCore p ↥X} (he : e ∈ barX p X (Subgroup.zpowers d)) (he1 : e ≠ 1)
    {L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)}
    (hL : IsComponentOf L (⨆ C' : 𝒞, barX p X (C' : Subgroup G))) :
    GLBConj e L ≠ L := by
  intro hfix
  obtain ⟨C, hC, rfl⟩ := idiag_component_eq hcomp hL
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 he
  have hxd : (x : G) ∈ Subgroup.zpowers d := Subgroup.mem_subgroupOf.1 hx
  have hxD : (x : G) ∈ D := (Subgroup.zpowers_le.2 hd) hxd
  have h1 : barX p X (GLBConj (x : G) C) = barX p X C := by
    rw [i183v_barX_gLBConj x.2 C]
    exact hfix
  have hCX : C ≤ X := (hcomp C hC).1
  have hxC : GLBConj (x : G) C = C := by
    have hcomp' : GLAPComponent p X (GLBConj (x : G) C) := by
      have := glaPComponent_gLBConj (hcomp C hC) (x : G)
      rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer x.2)] at this
    exact glaPComponent_unique hcomp' (hcomp C hC) h1
  have hxA : (x : G) ∈ A :=
    idiag_stab hp hAD hidx hAX hCX hC (hne C hC) htrans hxD hxC
  have hx1 : (x : G) = 1 := idiag_zcap hp hD hd hdA hxd hxA
  apply he1
  rw [show x = 1 from Subtype.ext hx1, map_one]

end Action

section Lift

variable {G : Type} [Group G] [Finite G]

theorem idiag_mem_core_of_mk_eq_one {p : ℕ} {X : Subgroup G} {u : G} (hu : u ∈ X)
    (h : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨u, hu⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = 1) :
    u ∈ GLAPPrimeCoreOf p X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact Subgroup.mem_map.2 ⟨⟨u, hu⟩, h, rfl⟩

theorem idiag_core_inf_le {p : ℕ} (hp : p.Prime) {X H : Subgroup G} (hHX : H ≤ X) :
    GLAPPrimeCoreOf p X ⊓ H ≤ GLAPPrimeCoreOf p H := by
  have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp X H
  rwa [inf_eq_right.2 hHX] at h1

theorem idiag_centMod {p : ℕ} (hp : p.Prime) {X C : Subgroup G} (hC : GLAPComponent p X C)
    {n : G} (hnX : n ∈ X)
    (hn : ∀ c ∈ barX p X C, Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨n, hnX⟩) c) :
    n ∈ centModSubgroup p C := by
  have hCX : C ≤ X := hC.1
  have hcent : ∀ y ∈ barX p X C, QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨n, hnX⟩ * y =
      y * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨n, hnX⟩ := fun y hy => (hn y hy).eq
  have hbar : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨n, hnX⟩) (barX p X C) =
      barX p X C := idiag_gLBConj_eq_of_comm hcent
  have hcomp' : GLAPComponent p X (GLBConj n C) := by
    have := glaPComponent_gLBConj hC n
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hnX)] at this
  have hbarC : barX p X (GLBConj n C) = barX p X C := by
    rw [i183v_barX_gLBConj hnX C, hbar]
  have hnorm : n ∈ Subgroup.normalizer (C : Set G) :=
    mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique hcomp' hC hbarC)
  refine mem_centModSubgroup.2 ⟨hnorm, fun l hl => ?_⟩
  have hlX : l ∈ X := hCX hl
  have hcomm : Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩)
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨n, hnX⟩) :=
    (hn _ (Subgroup.mem_map.2 ⟨⟨l, hlX⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩)).symm
  have hu : ⁅l, n⁆ ∈ C := by
    rw [commutatorElement_def]
    have h1 : n * l⁻¹ * n⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 hnorm l⁻¹).1 (C.inv_mem hl)
    have := C.mul_mem hl h1
    simpa [mul_assoc] using this
  have hu1 : ⁅l, n⁆ ∈ X := X.mul_mem (X.mul_mem (X.mul_mem hlX hnX) (X.inv_mem hlX))
    (X.inv_mem hnX)
  have hO : ⁅l, n⁆ ∈ GLAPPrimeCoreOf p X := by
    apply idiag_mem_core_of_mk_eq_one hu1
    have e : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨⁅l, n⁆, hu1⟩ :
        ↥X ⧸ GLAPPrimeCore p ↥X) =
        ⁅QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩,
          QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨n, hnX⟩⁆ := by
      simp only [commutatorElement_def, map_mul, map_inv]
      rfl
    rw [e, commutatorElement_eq_one_iff_commute]
    exact hcomm
  exact idiag_core_inf_le hp hCX (Subgroup.mem_inf.2 ⟨hO, hu⟩)

end Lift

section JPart

variable {G : Type} [Group G] [Finite G]

theorem idiag_barX_le_kb {p : ℕ} {X J : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hJK : J ≤ ⨆ C : 𝒞, (C : Subgroup G)) :
    barX p X J ≤ ⨆ C : 𝒞, barX p X (C : Subgroup G) := by
  intro x hx
  obtain ⟨⟨j, hjX⟩, hj, rfl⟩ := Subgroup.mem_map.1 hx
  have key : ∀ y ∈ (⨆ C : 𝒞, (C : Subgroup G)), ∃ hy : y ∈ X,
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hy⟩ ∈ (⨆ C : 𝒞, barX p X (C : Subgroup G)) := by
    intro y hy
    refine Subgroup.iSup_induction (fun C : 𝒞 => (C : Subgroup G))
      (C := fun y => ∃ hy : y ∈ X,
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hy⟩ ∈
          (⨆ C : 𝒞, barX p X (C : Subgroup G))) hy ?_ ?_ ?_
    · intro C y hyC
      have hyX : y ∈ X := (hcomp _ C.2).1 hyC
      refine ⟨hyX, le_iSup (fun C' : 𝒞 => barX p X (C' : Subgroup G)) C ?_⟩
      exact Subgroup.mem_map.2 ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.2 hyC, rfl⟩
    · refine ⟨X.one_mem, ?_⟩
      rw [show (⟨(1 : G), X.one_mem⟩ : ↥X) = 1 from Subtype.ext rfl, map_one]
      exact Subgroup.one_mem _
    · rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
      refine ⟨X.mul_mem ha hb, ?_⟩
      rw [show (⟨a * b, X.mul_mem ha hb⟩ : ↥X) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
      exact Subgroup.mul_mem _ hA hB
  obtain ⟨_, hmem⟩ := key j (hJK (Subgroup.mem_subgroupOf.1 hj))
  exact hmem

theorem idiag_barX_le_centralizer {p : ℕ} {X J D : Subgroup G} {d : G}
    (hJD : J ≤ Subgroup.centralizer (D : Set G)) (hd : d ∈ D) (hzd : Subgroup.zpowers d ≤ D) :
    barX p X J ≤ Subgroup.centralizer (barX p X (Subgroup.zpowers d) : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  intro x hx
  obtain ⟨⟨j, hjX⟩, hj, rfl⟩ := Subgroup.mem_map.1 hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨⟨z, hzX⟩, hz, rfl⟩ := Subgroup.mem_map.1 hh
  have hzD : z ∈ D := hzd (Subgroup.mem_subgroupOf.1 hz)
  have hcomm : z * j = j * z := Subgroup.mem_centralizer_iff.1 (hJD (Subgroup.mem_subgroupOf.1 hj)) z hzD
  show QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨z, hzX⟩ : ↥X) *
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨j, hjX⟩ : ↥X) =
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨j, hjX⟩ : ↥X) *
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨z, hzX⟩ : ↥X)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm

theorem idiag_layer_le {p : ℕ} (hp : p.Prime) {A D X : Subgroup G} {d : G}
    (hAD : A ≤ D) (hidx : A.relIndex D = p) (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a)
    (hD : IsElemAbelian p D) (hd : d ∈ D) (hdX : d ∈ X) (hdA : d ∉ A)
    {Dl : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)}
    (hDl : Dl ≤ Subgroup.centralizer (barX p X (Subgroup.zpowers d) : Set (↥X ⧸ GLAPPrimeCore p ↥X))) :
    Dl ≤ barX p X (Subgroup.centralizer (D : Set G)) := by
  have hzd : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.2 hd
  have hEp : IsPGroup p ↥(Subgroup.zpowers d) :=
    isPGroup_of_isElemAbelian' (idiag_elemAbelian_zpowers (hD.2 d hd))
  have hcen := i183_centralizer_barX_le hp (Subgroup.zpowers_le.2 hdX) hEp
  refine hDl.trans (hcen.trans (barX_mono p ?_))
  intro x hx
  obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨a, ha, k, rfl⟩ := idiag_decomp hp hD hAD hidx hd hdA h hh
  have hax : a * x = x * a := hAX a ha x hxX
  have hdx : d ^ k * x = x * d ^ k :=
    Subgroup.mem_centralizer_iff.1 hxC (d ^ k) (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) k)
  calc (a * d ^ k) * x = a * (d ^ k * x) := by group
    _ = a * (x * d ^ k) := by rw [hdx]
    _ = (a * x) * d ^ k := by group
    _ = (x * a) * d ^ k := by rw [hax]
    _ = x * (a * d ^ k) := by group

theorem idiag_barX_ne_bot {p : ℕ} (hp : p.Prime) {X H J : Subgroup G} (hJ : GLAPComponent p H J)
    (hHX : H ≤ X) : barX p X J ≠ ⊥ := by
  intro hbot
  have hJX : J ≤ X := hJ.1.trans hHX
  have hJO : J ≤ GLAPPrimeCoreOf p X := (i183_barX_eq_bot_iff hJX).1 hbot
  have h2 : J ≤ GLAPPrimeCoreOf p H := fun j hj =>
    idiag_core_inf_le hp hHX ⟨hJO hj, hJ.1 hj⟩
  have h3 : barX p H J = ⊥ := (i183_barX_eq_bot_iff hJ.1).2 h2
  have hnt := Quasisimple.nontrivial hJ.2.2.1.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt h3

end JPart

section Final

variable {G : Type} [Group G] [Finite G]

theorem idiag_barX_le_layer {p : ℕ} {X H J : Subgroup G} (hJ : GLAPComponent p H J) (hJX : J ≤ X)
    {Kb C Dl W : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} (hC : C = Dl ⊔ W) (hCK : C ≤ Kb)
    (hWK : W ≤ Kb) (hW : ∀ w ∈ W, ∀ g ∈ Kb, Commute w g) (hJC : barX p X J ≤ C) :
    barX p X J ≤ Dl := by
  have hcomm := i183v_comm_le hC hCK hWK hW
  have hperf : ⁅barX p X J, barX p X J⁆ = barX p X J := by
    rw [← barX_commutator p hJX hJX, glaPComponent_perfect hJ]
  calc barX p X J = ⁅barX p X J, barX p X J⁆ := hperf.symm
    _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hJC hJC
    _ ≤ Dl := hcomm

theorem idiag_layer_le_barX {p : ℕ} (hp : p.Prime) {X H J : Subgroup G}
    (hJ : GLAPComponent p H J) (hJX : J ≤ X) (hHX : H ≤ X)
    {Dl : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} (hDle : Dl ≤ barX p X H)
    (hquasi : CFSG.Open.IsQuasisimple ↥Dl) (hJDl : barX p X J ≤ Dl) :
    Dl ≤ barX p X J := by
  have hsn : IsSubnormal (barX p X J) Dl :=
    isSubnormal_of_le_of_le (isSubnormal_barX p (C := X) hJ.2.1) hJDl hDle
  rcases i183v_eq_or_le_center hsn hquasi with h | h
  · exact h.symm.le
  · exfalso
    have hab : ⁅barX p X J, barX p X J⁆ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.1 (h hy)
      have hzD : z ∈ Dl := hJDl hz
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨z, hzD⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_mk] at this
      rw [← hcy]
      exact this
    have hperf : ⁅barX p X J, barX p X J⁆ = barX p X J := by
      rw [← barX_commutator p hJX hJX, glaPComponent_perfect hJ]
    exact idiag_barX_ne_bot hp hJ hHX (hperf.symm.trans hab)

end Final

section Helpers2

variable {G : Type} [Group G] [Finite G]

theorem idiag_pow_ne_one {p : ℕ} (hp : p.Prime) {A D : Subgroup G} (hD : IsElemAbelian p D)
    {d : G} (hd : d ∈ D) (hdA : d ∉ A) {n : ℕ} (hn0 : 0 < n) (hnp : n < p) : d ^ n ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have hdp : d ^ p = 1 := hD.2 d hd
  have hd1 : d ≠ 1 := fun h1 => hdA (h1 ▸ A.one_mem)
  have hord : orderOf d = p := orderOf_eq_prime hdp hd1
  have hdvd : orderOf d ∣ n := orderOf_dvd_of_pow_eq_one h
  rw [hord] at hdvd
  exact absurd (Nat.le_of_dvd hn0 hdvd) (by omega)

theorem idiag_gc_ne {p : ℕ} (hp : p.Prime) {A D X C : Subgroup G} {𝒞 : Set (Subgroup G)} {d : G}
    (hAD : A ≤ D) (hidx : A.relIndex D = p) (hD : IsElemAbelian p D) (hd : d ∈ D) (hdA : d ∉ A)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a) (hCX : C ≤ X) (hC : C ∈ 𝒞)
    (hne : ∃ C₂ ∈ 𝒞, C₂ ≠ C)
    (htrans : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ D, GLBConj e C = C')
    {n : ℕ} (hn0 : 0 < n) (hnp : n < p) (hdn : d ^ n ∈ D) : GLBConj (d ^ n) C ≠ C := by
  intro hfix
  have hA := idiag_stab hp hAD hidx hAX hCX hC hne htrans hdn hfix
  have h1 := idiag_zcap hp hD hd hdA (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) n) hA
  exact idiag_pow_ne_one hp hD hd hdA hn0 hnp h1

theorem idiag_E_pow {p : ℕ} {X : Subgroup G} {d : G} (hdX : d ∈ X)
    {e : ↥X ⧸ GLAPPrimeCore p ↥X} (he : e ∈ barX p X (Subgroup.zpowers d)) :
    ∃ k : ℤ, e = (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d, hdX⟩) ^ k := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 he
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hx)
  refine ⟨k, ?_⟩
  rw [← map_zpow]
  congr 1
  exact Subtype.ext (by simp [← hk])

theorem idiag_conj_list {Y : Type*} [Group Y] (c : Y) (f : ℕ → Y)
    (hf : ∀ n, c⁻¹ * f n * c = f (n + 1)) :
    ∀ (k s : ℕ), c⁻¹ * (List.map f (List.range' s k)).prod * c =
      (List.map f (List.range' (s + 1) k)).prod := by
  intro k
  induction k with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    simp only [List.range'_succ, List.map_cons, List.prod_cons]
    have e1 : c⁻¹ * (f s * (List.map f (List.range' (s + 1) k)).prod) * c =
        (c⁻¹ * f s * c) * (c⁻¹ * (List.map f (List.range' (s + 1) k)).prod * c) := by group
    rw [e1, hf s, ih (s + 1)]

end Helpers2

section Lifting

variable {G : Type} [Group G] [Finite G]

theorem idiag_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A D X : Subgroup G} {d : G} {𝒞 : Set (Subgroup G)} {J : Subgroup G}
    (hAD : A ≤ D) (hidx : A.relIndex D = p) (hD : IsElemAbelian p D) (hd : d ∈ D)
    (hdX : d ∈ X) (hdA : d ∉ A) (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a)
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hinv : ∀ C ∈ 𝒞, ∀ e ∈ D, GLBConj e C ∈ 𝒞)
    (hne : ∀ C ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₂ ≠ C)
    (htrans : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ D, GLBConj e C = C')
    {C : Subgroup G} (hC : C ∈ 𝒞) {m : G} (hm : m ∈ C)
    {Kb Dl W : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)}
    (hKb : Kb = ⨆ C' : 𝒞, barX p X (C' : Subgroup G))
    (hsplit : Kb ⊓ Subgroup.centralizer
        (barX p X (Subgroup.zpowers d) : Set (↥X ⧸ GLAPPrimeCore p ↥X)) = Dl ⊔ W)
    (hWK : W ≤ Kb) (hW : ∀ w ∈ W, ∀ g ∈ Kb, Commute w g)
    (hDJ : Dl ≤ barX p X J) :
    ∃ j ∈ J, ∃ n ∈ centModSubgroup p C, m = j * n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp : d ^ p = 1 := hD.2 d hd
  have hCX : C ≤ X := (hcomp C hC).1
  have hmX : m ∈ X := hCX hm
  have hdnX : ∀ n : ℕ, d ^ n ∈ X := fun n => X.pow_mem hdX n
  have hdnD : ∀ n : ℕ, d ^ n ∈ D := fun n => D.pow_mem hd n
  have hconjX : ∀ n : ℕ, (d ^ n)⁻¹ * m * d ^ n ∈ X := fun n =>
    X.mul_mem (X.mul_mem (X.inv_mem (hdnX n)) hmX) (hdnX n)
  have hbarLe : ∀ C' ∈ 𝒞, barX p X C' ≤ Kb := fun C' hC' => by
    rw [hKb]
    exact le_iSup (fun C'' : 𝒞 => barX p X (C'' : Subgroup G)) ⟨C', hC'⟩
  obtain ⟨eb, heb⟩ : ∃ eb : ↥X ⧸ GLAPPrimeCore p ↥X,
      eb = QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d, hdX⟩ := ⟨_, rfl⟩
  obtain ⟨yy, hyy⟩ : ∃ yy : ℕ → ↥X ⧸ GLAPPrimeCore p ↥X,
      ∀ n, yy n = QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(d ^ n)⁻¹ * m * d ^ n, hconjX n⟩ :=
    ⟨_, fun n => rfl⟩
  have hyy_mem : ∀ n : ℕ, yy n ∈ barX p X (GLBConj (d ^ n) C) := by
    intro n
    rw [hyy n]
    refine Subgroup.mem_map.2 ⟨⟨(d ^ n)⁻¹ * m * d ^ n, hconjX n⟩, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    rw [mem_gLBConj]
    have e : d ^ n * ((d ^ n)⁻¹ * m * d ^ n) * (d ^ n)⁻¹ = m := by group
    rw [e]
    exact hm
  have hyy_Kb : ∀ n : ℕ, yy n ∈ Kb := fun n =>
    hbarLe _ (hinv C hC (d ^ n) (hdnD n)) (hyy_mem n)
  have hyy0 : yy 0 = QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨m, hmX⟩ := by
    rw [hyy 0]
    congr 1
    exact Subtype.ext (by simp)
  have hyy0_mem : yy 0 ∈ barX p X C := by
    rw [hyy0]
    exact Subgroup.mem_map.2 ⟨⟨m, hmX⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
  have hyyp : yy p = yy 0 := by
    rw [hyy p, hyy 0]
    congr 1
    exact Subtype.ext (by simp [hdp])
  have hshift : ∀ n : ℕ, eb⁻¹ * yy n * eb = yy (n + 1) := by
    intro n
    rw [heb, hyy n, hyy (n + 1)]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, pow_succ, mul_inv_rev]; group)
  have hcommn : ∀ n : ℕ, 0 < n → n < p → ∀ c ∈ barX p X C, Commute (yy n) c := by
    intro n hn0 hnp c hc
    have hne' : GLBConj (d ^ n) C ≠ C :=
      idiag_gc_ne hp hAD hidx hD hd hdA hAX hCX hC (hne C hC) htrans hn0 hnp (hdnD n)
    have hcm := idiag_barX_commute (hcomp _ (hinv C hC (d ^ n) (hdnD n))) (hcomp C hC) hne'
    have hsub := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcm (hyy_mem n)
    exact (Subgroup.mem_centralizer_iff.1 hsub c hc).symm
  obtain ⟨Q, hQ⟩ : ∃ Q : ↥X ⧸ GLAPPrimeCore p ↥X,
      Q = (List.map yy (List.range' 1 (p - 1))).prod := ⟨_, rfl⟩
  have hQcent : Q ∈ Subgroup.centralizer (barX p X C : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rw [hQ]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range'_1] at hn
    refine Subgroup.mem_centralizer_iff.2 (fun c hc => ?_)
    exact (hcommn n (by omega) (by omega) c hc).eq.symm
  have hQKb : Q ∈ Kb := by
    rw [hQ]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx
    exact hyy_Kb n
  have hcommQ0 : Commute (yy 0) Q := by
    rw [hQ]
    refine Commute.list_prod_right _ _ (fun x hx => ?_)
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range'_1] at hn
    exact (hcommn n (by omega) (by omega) (yy 0) hyy0_mem).symm
  have hconjQ : eb⁻¹ * Q * eb = (List.map yy (List.range' 2 (p - 1))).prod := by
    rw [hQ]
    exact idiag_conj_list eb yy hshift (p - 1) 1
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨R, hR⟩ : ∃ R : ↥X ⧸ GLAPPrimeCore p ↥X,
      R = (List.map yy (List.range' 2 (p - 2))).prod := ⟨_, rfl⟩
  have hQsplit : Q = yy 1 * R := by
    rw [hQ, hR]
    have e1 : p - 1 = (p - 2) + 1 := by omega
    rw [e1, List.range'_succ]
    simp only [List.map_cons, List.prod_cons]
  have hQ'split : (List.map yy (List.range' 2 (p - 1))).prod = R * yy p := by
    rw [hR]
    have e1 : p - 1 = (p - 2) + 1 := by omega
    have e2 : 2 + (p - 2) = p := by omega
    rw [e1, List.range'_concat]
    simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, e2]
  obtain ⟨g, hg⟩ : ∃ g : ↥X ⧸ GLAPPrimeCore p ↥X, g = yy 0 * Q := ⟨_, rfl⟩
  have hg_conj : eb⁻¹ * g * eb = g := by
    rw [hg]
    calc eb⁻¹ * (yy 0 * Q) * eb = (eb⁻¹ * yy 0 * eb) * (eb⁻¹ * Q * eb) := by group
      _ = yy 1 * (R * yy p) := by
        rw [hconjQ, hQ'split]
        exact congrArg (fun z => z * (R * yy p)) (hshift 0)
      _ = (yy 1 * R) * yy p := by group
      _ = Q * yy p := by rw [← hQsplit]
      _ = Q * yy 0 := by rw [hyyp]
      _ = yy 0 * Q := hcommQ0.eq.symm
  have hcommEg : Commute eb g := by
    have h1 : eb * (eb⁻¹ * g * eb) = eb * g := by rw [hg_conj]
    have h2 : eb * (eb⁻¹ * g * eb) = g * eb := by group
    exact h1.symm.trans h2
  have hgKb : g ∈ Kb := by
    rw [hg]
    exact Kb.mul_mem (hyy_Kb 0) hQKb
  have hgE : g ∈ Subgroup.centralizer
      (barX p X (Subgroup.zpowers d) : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    refine Subgroup.mem_centralizer_iff.2 (fun e he => ?_)
    obtain ⟨k, hk⟩ := idiag_E_pow hdX he
    rw [hk, ← heb]
    exact (hcommEg.zpow_left k).eq
  have hg_split : g ∈ Dl ⊔ W := by
    rw [← hsplit]
    exact ⟨hgKb, hgE⟩
  have hDle : Dl ≤ Kb ⊓ Subgroup.centralizer
      (barX p X (Subgroup.zpowers d) : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rw [hsplit]
    exact le_sup_left
  have hDlKb : Dl ≤ Kb := fun x hx => (hDle hx).1
  have hWN : W ≤ Subgroup.normalizer (Dl : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := fun w hw =>
    mem_normalizer_iff_gLBConj_eq.2
      (idiag_gLBConj_eq_of_comm (fun y hy => (hW w hw y (hDlKb hy)).eq))
  have hgsup : g ∈ (↑(Dl ⊔ W) : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := hg_split
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Dl W hWN] at hgsup
  obtain ⟨δ, hδ, w, hw, hδw⟩ := Set.mem_mul.1 hgsup
  obtain ⟨⟨j, hjX⟩, hjJ, hjδ⟩ := Subgroup.mem_map.1 (hDJ hδ)
  have hjJ' : j ∈ J := Subgroup.mem_subgroupOf.1 hjJ
  have hnX : j⁻¹ * m ∈ X := X.mul_mem (X.inv_mem hjX) hmX
  have hy0 : yy 0 = δ * w * Q⁻¹ := by
    rw [hδw, hg, mul_inv_cancel_right]
  have hmk : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨j⁻¹ * m, hnX⟩ = w * Q⁻¹ := by
    have e1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨j⁻¹ * m, hnX⟩ =
        (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨j, hjX⟩)⁻¹ *
          QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨m, hmX⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e1, hjδ, ← hyy0, hy0]
    group
  have hcomm_final : ∀ c ∈ barX p X C,
      Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨j⁻¹ * m, hnX⟩) c := by
    intro c hc
    rw [hmk]
    refine Commute.mul_left (hW w hw c (hbarLe C hC hc)) ?_
    have hQc : Commute Q c := (Subgroup.mem_centralizer_iff.1 hQcent c hc).symm
    exact hQc.inv_left
  have hnC : j⁻¹ * m ∈ centModSubgroup p C := idiag_centMod hp (hcomp C hC) hnX hcomm_final
  exact ⟨j, hjJ', j⁻¹ * m, hnC, (mul_inv_cancel_left j m).symm⟩

end Lifting


theorem i183DiagAt_holds (G : Type) [Group G] [Finite G] (p : ℕ) : I183DiagAt G p := by
  intro hp hp2 A D J 𝒞 hD hAD hidx _hX hJ hcomp hsup hinv htrans hne0
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := Subgroup.centralizer (A : Set G) with hXdef
  have hAX : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a := fun a ha x hx =>
    Subgroup.mem_centralizer_iff.1 hx a ha
  have hne : ∀ C ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₂ ≠ C := by
    intro C hC
    obtain ⟨C₁, h₁, C₂, h₂, h12⟩ := hne0
    by_cases h : C = C₁
    · exact ⟨C₂, h₂, fun e => h12 (e.trans h).symm⟩
    · exact ⟨C₁, h₁, fun e => h e.symm⟩
  obtain ⟨d, hd, hdA⟩ : ∃ d ∈ D, d ∉ A := by
    by_contra hcon
    push Not at hcon
    have h1 : A.relIndex D = 1 := Subgroup.relIndex_eq_one.2 (fun x hx => hcon x hx)
    have h2 : A.relIndex D = p := hidx
    rw [h2] at h1
    exact (hp.one_lt.ne') h1
  have hdX : d ∈ X := Subgroup.mem_centralizer_iff.2 (fun a ha => idiag_commute hD (hAD ha) hd)
  have hdp : d ^ p = 1 := hD.2 d hd
  have hzd : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.2 hd
  have hJX : J ≤ X := hJ.1.trans (Subgroup.centralizer_le (fun x hx => hAD hx))
  have hHX : Subgroup.centralizer (D : Set G) ≤ X :=
    Subgroup.centralizer_le (fun x hx => hAD hx)
  set Kb : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := ⨆ C' : 𝒞, barX p X (C' : Subgroup G) with hKb
  set E : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := barX p X (Subgroup.zpowers d) with hE
  have hlay : GLALayer Kb = Kb := by
    refine le_antisymm (i25_layer_le Kb) ?_
    exact iSup_le fun C' => i25_le_layer (idiag_barX_isComponent hcomp C'.2)
  have hEnorm : E ≤ Subgroup.normalizer (Kb : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    idiag_E_le_normalizer hinv hd hdX
  have hEab : IsElemAbelian p E := isElemAbelian_barX (idiag_elemAbelian_zpowers hdp)
  have htr : ∀ L L' : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X), IsComponentOf L Kb →
      IsComponentOf L' Kb → ∃ e ∈ E, GLBConj e L = L' := fun L L' hL hL' =>
    idiag_trans hp hD hAD hidx hd hdA hdX hAX hcomp htrans hL hL'
  have hfree : ∀ e ∈ E, e ≠ 1 → ∀ L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X),
      IsComponentOf L Kb → GLBConj e L ≠ L := fun e he he1 L hL =>
    idiag_free hp hD hAD hidx hd hdA hdX hAX hcomp hne htrans he he1 hL
  have hI25 := input2_5_proved _ p hp Kb E hlay hEnorm hEab htr hfree
  obtain ⟨hI25a, hI25b⟩ := hI25
  obtain ⟨Dl, hDl⟩ : ∃ Dl : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X),
      Dl = GLALayer (Kb ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X))) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X),
      W = (Subgroup.center ↥Kb).map Kb.subtype ⊓
        Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := ⟨_, rfl⟩
  have hsplit : Kb ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) = Dl ⊔ W := by
    rw [hDl, hW]
    exact hI25b
  have hWK : W ≤ Kb := by
    rw [hW]
    exact inf_le_left.trans (Subgroup.map_subtype_le _)
  have hWc : ∀ w ∈ W, ∀ g ∈ Kb, Commute w g := by
    intro w hw g hg
    rw [hW] at hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw.1
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)).symm
  have hJsup : J ≤ ⨆ C' : 𝒞, (C' : Subgroup G) := by
    have h1 : J ≤ ⨆ g ∈ GLAPLayer p X, GLBConj g J :=
      (gLBConj_one J).symm.le.trans
        (le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer p X) => GLBConj g J) (1 : G) (Subgroup.one_mem _))
    rw [← hsup] at h1
    exact h1.trans (iSup_subtype' (p := fun C : Subgroup G => C ∈ 𝒞) (f := fun C _ => C)).le
  have hbarJK : barX p X J ≤ Kb := idiag_barX_le_kb hcomp hJsup
  have hbarJC : barX p X J ≤ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    idiag_barX_le_centralizer hJ.1 hd hzd
  have hbarJKC : barX p X J ≤ Kb ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    le_inf hbarJK hbarJC
  have hJDl : barX p X J ≤ Dl := idiag_barX_le_layer hJ hJX hsplit inf_le_left hWK hWc hbarJKC
  have hDle : Dl ≤ Kb ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rw [hsplit]
    exact le_sup_left
  have hDlC : Dl ≤ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    fun x hx => (hDle hx).2
  have hDlbar : Dl ≤ barX p X (Subgroup.centralizer (D : Set G)) :=
    idiag_layer_le hp hAD hidx hAX hD hd hdX hdA hDlC
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Subgroup G, C₁ ∈ 𝒞 := by
    obtain ⟨C₁, h₁, -⟩ := hne0
    exact ⟨C₁, h₁⟩
  obtain ⟨Z, hZn, hZc, ⟨φ⟩⟩ := hI25a _ (idiag_barX_isComponent hcomp hC₁)
  have hDq : CFSG.Open.IsQuasisimple ↥Dl := by
    rw [hDl]
    exact Components.quasisimple_of_equiv φ
      (Quasisimple.central_quotient (idiag_barX_isComponent hcomp hC₁).2.2 Z hZc)
  have hDJ : Dl ≤ barX p X J :=
    idiag_layer_le_barX hp hJ hJX hHX hDlbar hDq hJDl
  intro C hC
  intro m hm
  obtain ⟨j, hj, n, hn, rfl⟩ := idiag_lift hp hp2 hAD hidx hD hd hdX hdA hAX hcomp hinv hne htrans
    hC hm hKb hsplit hWK hWc hDJ
  exact Subgroup.mul_mem_sup hj hn

end CFSG.LocalAnalysis.GLTheoremA

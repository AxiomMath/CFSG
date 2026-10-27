module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFB
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFQ9

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

section Final

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem inj_of_KA {K : Subgroup G} (hKC : K ≤ Cen z) (hKA : ∀ x ∈ K, x ∈ OddCore z → x = 1) :
    Function.Injective ((toBar z).comp (Subgroup.inclusion hKC)) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have h1 : (Subgroup.inclusion hKC b) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 hb
  have h2 : (b : G) ∈ OddCore z := ⟨_, h1, rfl⟩
  exact Subtype.ext (hKA b b.2 h2)

theorem z_mem_of_KA {K : Subgroup G} {L : Subgroup (CentralizerBar z)} (hz2 : z * z = 1)
    (hodd : ∀ a ∈ OddCore z, ∀ l ∈ Em (Cen z), a * l = l * a) (hKE : K ≤ Em (Cen z))
    (hbar : barOf z K = L) (hzL : toBar z ⟨z, mem_Cen_self z⟩ ∈ L)
    (hKA : ∀ x ∈ K, x ∈ OddCore z → x = 1) : z ∈ K := by
  have hzL' : toBar z ⟨z, mem_Cen_self z⟩ ∈ barOf z K := hbar ▸ hzL
  obtain ⟨k, hkC, hkK, hk⟩ := bar_mem_barOf_iff.1 hzL'
  have hkE : k ∈ Em (Cen z) := hKE hkK
  have haC : k⁻¹ * z ∈ Cen z := (Cen z).mul_mem ((Cen z).inv_mem hkC) (mem_Cen_self z)
  have haA : k⁻¹ * z ∈ OddCore z := by
    have h1 : toBar z ⟨k⁻¹ * z, haC⟩ = 1 := by
      have : (⟨k⁻¹ * z, haC⟩ : ↥(Cen z)) = ⟨k, hkC⟩⁻¹ * ⟨z, mem_Cen_self z⟩ := rfl
      rw [this, map_mul, map_inv, hk, inv_mul_cancel]
    exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  set a := k⁻¹ * z with ha
  have hcomm : a * k = k * a := hodd a haA k hkE
  have hz : z = k * a := by simp only [ha]; group
  have hsq : (k * k) * (a * a) = 1 := by
    calc (k * k) * (a * a) = k * (k * a) * a := by group
      _ = k * (a * k) * a := by rw [← hcomm]
      _ = (k * a) * (k * a) := by group
      _ = 1 := by rw [← hz]; exact hz2
  have hkk : k * k ∈ OddCore z := by
    have : k * k = (a * a)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact (OddCore z).inv_mem ((OddCore z).mul_mem haA haA)
  have hkk1 : k * k = 1 := hKA _ (K.mul_mem hkK hkK) hkk
  have haa1 : a * a = 1 := by rw [hkk1, one_mul] at hsq; exact hsq
  have hodda : Odd (orderOf a) := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.odd_orderOf_of_mem_pPrimeCoreOf
    (F := Cen z) haA
  have ha1 : a = 1 := eq_one_of_sq_odd_nf haa1 hodda
  rw [hz, ha1, mul_one]
  exact hkK

theorem NFCtx.z_mem_K₁ (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) (hKA : ∀ x ∈ K₁, x ∈ OddCore z → x = 1) :
    z ∈ K₁ :=
  z_mem_of_KA h.z2 h.comp.oddcomm (h.comp.layer ▸ le_sup_left) h.comp.bar₁ h.zbar_mem.1 hKA

theorem NFCtx.z_mem_K₂ (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) (hKA : ∀ x ∈ K₂, x ∈ OddCore z → x = 1) :
    z ∈ K₂ :=
  z_mem_of_KA h.z2 h.comp.oddcomm (h.comp.layer ▸ le_sup_right) h.comp.bar₂ h.zbar_mem.2 hKA

theorem NFCtx.card_inf_two (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) (hKA₁ : ∀ x ∈ K₁, x ∈ OddCore z → x = 1)
    (hKA₂ : ∀ x ∈ K₂, x ∈ OddCore z → x = 1) : Nat.card ↥(K₁ ⊓ K₂) = 2 := by
  have hz₁ := h.z_mem_K₁ hKA₁
  have hz₂ := h.z_mem_K₂ hKA₂
  have hinj₁ := inj_of_KA h.comp.le₁ hKA₁
  obtain ⟨-, -, hcard⟩ := h.pair.prod
  have hle : Nat.card ↥(K₁ ⊓ K₂) ≤ 2 := by
    rw [← hcard]
    let f : ↥(K₁ ⊓ K₂) →* ↥(L₁ ⊓ L₂) :=
      { toFun := fun x => ⟨toBar z ⟨(x : G), h.comp.le₁ x.2.1⟩, by
          have m₁ : toBar z ⟨(x : G), h.comp.le₁ x.2.1⟩ ∈ barOf z K₁ :=
            bar_mem_barOf_iff.2 ⟨x, h.comp.le₁ x.2.1, x.2.1, rfl⟩
          have m₂ : toBar z ⟨(x : G), h.comp.le₁ x.2.1⟩ ∈ barOf z K₂ :=
            bar_mem_barOf_iff.2 ⟨x, h.comp.le₂ x.2.2, x.2.2, rfl⟩
          exact ⟨h.comp.bar₁ ▸ m₁, h.comp.bar₂ ▸ m₂⟩⟩
        map_one' := by apply Subtype.ext; exact (map_one (toBar z) : toBar z 1 = 1)
        map_mul' := fun a b => by
          apply Subtype.ext
          exact map_mul (toBar z) ⟨(a : G), h.comp.le₁ a.2.1⟩ ⟨(b : G), h.comp.le₁ b.2.1⟩ }
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 : toBar z ⟨(a : G), h.comp.le₁ a.2.1⟩ = toBar z ⟨(b : G), h.comp.le₁ b.2.1⟩ :=
        congrArg Subtype.val hab
      have h2 := @hinj₁ ⟨(a : G), a.2.1⟩ ⟨(b : G), b.2.1⟩ h1
      have h3 : ((⟨(a : G), a.2.1⟩ : ↥K₁) : G) = ((⟨(b : G), b.2.1⟩ : ↥K₁) : G) := congrArg Subtype.val h2
      exact Subtype.ext h3
    exact Nat.card_le_card_of_injective f hfinj
  have hgt : 1 < Nat.card ↥(K₁ ⊓ K₂) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hb
    have : z ∈ (⊥ : Subgroup G) := hb ▸ (⟨hz₁, hz₂⟩ : z ∈ K₁ ⊓ K₂)
    exact h.z1 (Subgroup.mem_bot.mp this)
  omega


open CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2 in
theorem NFCtx.nrm_K₁ (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) (hKA₁ : ∀ x ∈ K₁, x ∈ OddCore z → x = 1)
    (hKA₂ : ∀ x ∈ K₂, x ∈ OddCore z → x = 1) {t : G} (htC : t ∈ Cen z) (ht2 : t * t = 1)
    (hn₁ : toBar z ⟨t, htC⟩ ∈ normalizer (L₁ : Set (CentralizerBar z))) : t ∈ normalizer (K₁ : Set G) := by
  have hz₁ := h.z_mem_K₁ hKA₁
  have hz₂ := h.z_mem_K₂ hKA₂
  have hz₀ := h.zbar_mem
  have p₁ := pair₁_of_stage1 h.pair
  have hz01 : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
    intro h1
    have := eq_one_of_toBar_eq_one z (x := ⟨z, mem_Cen_self z⟩) (Subtype.ext h.z2) h1
    exact h.z1 (congrArg Subtype.val this)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hforward : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₁ := by
    intro k hk
    set P : Subgroup G := K₁.map (MulAut.conj t).toMonoidHom with hP
    have hPC : P ≤ Cen z := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Cen z).mul_mem ((Cen z).mul_mem htC (h.comp.le₁ hy)) ((Cen z).inv_mem htC)
    have hPperf : ⁅P, P⁆ = P := by
      rw [hP, ← Subgroup.map_commutator, h.comp.perf₁]
    have hPE : P ≤ Em (Cen z) := h.comp.perfect P hPC hPperf
    have hkP : t * k * t⁻¹ ∈ P := ⟨k, hk, rfl⟩
    have hk'E : t * k * t⁻¹ ∈ K₁ ⊔ K₂ := h.comp.layer ▸ hPE hkP
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute h.comp.comm hk'E
    have hkb : toBar z ⟨k, h.comp.le₁ hk⟩ ∈ L₁ := by
      have : toBar z ⟨k, h.comp.le₁ hk⟩ ∈ barOf z K₁ := bar_mem_barOf_iff.2 ⟨k, h.comp.le₁ hk, hk, rfl⟩
      rwa [h.comp.bar₁] at this
    have hab' : toBar z ⟨a, h.comp.le₁ ha⟩ ∈ L₁ := by
      have : toBar z ⟨a, h.comp.le₁ ha⟩ ∈ barOf z K₁ := bar_mem_barOf_iff.2 ⟨a, h.comp.le₁ ha, ha, rfl⟩
      rwa [h.comp.bar₁] at this
    have hbb₂ : toBar z ⟨b, h.comp.le₂ hb⟩ ∈ L₂ := by
      have : toBar z ⟨b, h.comp.le₂ hb⟩ ∈ barOf z K₂ := bar_mem_barOf_iff.2 ⟨b, h.comp.le₂ hb, hb, rfl⟩
      rwa [h.comp.bar₂] at this
    have hk'C : t * k * t⁻¹ ∈ Cen z := (Cen z).mul_mem ((Cen z).mul_mem htC (h.comp.le₁ hk)) ((Cen z).inv_mem htC)
    have hbar : toBar z ⟨b, h.comp.le₂ hb⟩ = (toBar z ⟨a, h.comp.le₁ ha⟩)⁻¹ * toBar z ⟨t * k * t⁻¹, hk'C⟩ := by
      rw [← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      show b = a⁻¹ * (t * k * t⁻¹)
      rw [hab]; group
    have hbb₁ : toBar z ⟨b, h.comp.le₂ hb⟩ ∈ L₁ := by
      rw [hbar]
      refine L₁.mul_mem (L₁.inv_mem hab') ?_
      have e : toBar z ⟨t * k * t⁻¹, hk'C⟩ = toBar z ⟨t, htC⟩ * toBar z ⟨k, h.comp.le₁ hk⟩ * (toBar z ⟨t, htC⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]; rfl
      rw [e]
      have := (Subgroup.mem_normalizer_iff.1 hn₁ (toBar z ⟨k, h.comp.le₁ hk⟩)).1 hkb
      exact this
    have hbcases : b = 1 ∨ b = z := by
      rcases p₁.inf_cases hz₀ hz01 ⟨hbb₁, hbb₂⟩ with h1 | h1
      · left
        have : (⟨b, h.comp.le₂ hb⟩ : ↥(Cen z)) = 1 := by
          have hA : b ∈ OddCore z := ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
          exact Subtype.ext (hKA₂ b hb hA)
        exact congrArg Subtype.val this
      · right
        have hbz : b * z⁻¹ ∈ OddCore z := by
          have h2 : toBar z ⟨b * z⁻¹, (Cen z).mul_mem (h.comp.le₂ hb) ((Cen z).inv_mem (mem_Cen_self z))⟩ = 1 := by
            have : (⟨b * z⁻¹, (Cen z).mul_mem (h.comp.le₂ hb) ((Cen z).inv_mem (mem_Cen_self z))⟩ : ↥(Cen z)) =
                ⟨b, h.comp.le₂ hb⟩ * ⟨z, mem_Cen_self z⟩⁻¹ := rfl
            rw [this, map_mul, map_inv, h1, mul_inv_cancel]
          exact ⟨_, (QuotientGroup.eq_one_iff _).1 h2, rfl⟩
        have h3 := hKA₂ _ (K₂.mul_mem hb (K₂.inv_mem hz₂)) hbz
        exact mul_inv_eq_one.1 h3
    rw [hab]
    rcases hbcases with hb1 | hbz
    · rw [hb1, mul_one]; exact ha
    · rw [hbz]; exact K₁.mul_mem ha hz₁
  refine Subgroup.mem_normalizer_iff.2 (fun k => ⟨fun hk => hforward k hk, fun hk => ?_⟩)
  have := hforward _ hk
  have e : t * (t * k * t⁻¹) * t⁻¹ = k := by
    calc t * (t * k * t⁻¹) * t⁻¹ = (t * t) * k * (t⁻¹ * t⁻¹) := by group
      _ = k := by rw [htinv, ht2]; group
  rwa [e] at this


theorem NFCtx.card_O2_transport (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) (hKA₁ : ∀ x ∈ K₁, x ∈ OddCore z → x = 1)
    {t : G} (htC : t ∈ Cen z) (htN : t ∈ normalizer (K₁ : Set G)) :
    Nat.card ↥(pPrimeCoreOf 2 (K₁ ⊓ centralizer ({t} : Set G))) =
      Nat.card ↥(pPrimeCoreOf 2 (L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z)))) := by
  have hinj := inj_of_KA h.comp.le₁ hKA₁
  let f : ↥(K₁ ⊓ centralizer ({t} : Set G)) →*
      ↥(L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z))) :=
    { toFun := fun x => ⟨toBar z ⟨(x : G), h.comp.le₁ x.2.1⟩, by
        refine ⟨?_, ?_⟩
        · have : toBar z ⟨(x : G), h.comp.le₁ x.2.1⟩ ∈ barOf z K₁ :=
            bar_mem_barOf_iff.2 ⟨x, h.comp.le₁ x.2.1, x.2.1, rfl⟩
          exact h.comp.bar₁ ▸ this
        · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
          have hxt : (x : G) * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext hxt⟩
      map_one' := by apply Subtype.ext; exact (map_one (toBar z) : toBar z 1 = 1)
      map_mul' := fun a b => by
        apply Subtype.ext
        exact map_mul (toBar z) ⟨(a : G), h.comp.le₁ a.2.1⟩ ⟨(b : G), h.comp.le₁ b.2.1⟩ }
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : toBar z ⟨(a : G), h.comp.le₁ a.2.1⟩ = toBar z ⟨(b : G), h.comp.le₁ b.2.1⟩ :=
      congrArg Subtype.val hab
    have h2 := @hinj ⟨(a : G), a.2.1⟩ ⟨(b : G), b.2.1⟩ h1
    have h3 : ((⟨(a : G), a.2.1⟩ : ↥K₁) : G) = ((⟨(b : G), b.2.1⟩ : ↥K₁) : G) := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hyL, hyc⟩
    have hyK : y ∈ barOf z K₁ := h.comp.bar₁ ▸ hyL
    obtain ⟨k, hkC, hkK, rfl⟩ := bar_mem_barOf_iff.1 hyK
    have hyc' : toBar z ⟨k, hkC⟩ * toBar z ⟨t, htC⟩ = toBar z ⟨t, htC⟩ * toBar z ⟨k, hkC⟩ :=
      Subgroup.mem_centralizer_singleton_iff.1 hyc
    have hcomm : k * t = t * k := by
      have hC : k * t * k⁻¹ * t⁻¹ ∈ Cen z := (Cen z).mul_mem ((Cen z).mul_mem ((Cen z).mul_mem hkC htC)
        ((Cen z).inv_mem hkC)) ((Cen z).inv_mem htC)
      have h1 : toBar z ⟨k * t * k⁻¹ * t⁻¹, hC⟩ = 1 := by
        have : (⟨k * t * k⁻¹ * t⁻¹, hC⟩ : ↥(Cen z)) =
            ⟨k, hkC⟩ * ⟨t, htC⟩ * ⟨k, hkC⟩⁻¹ * ⟨t, htC⟩⁻¹ := rfl
        rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hyc']
        group
      have hA : k * t * k⁻¹ * t⁻¹ ∈ OddCore z := ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
      have hK : k * t * k⁻¹ * t⁻¹ ∈ K₁ := by
        have h2 := (Subgroup.mem_normalizer_iff.1 htN k⁻¹).1 (K₁.inv_mem hkK)
        have := K₁.mul_mem hkK h2
        simpa [mul_assoc] using this
      have h3 := hKA₁ _ hK hA
      calc k * t = (k * t * k⁻¹ * t⁻¹) * t * k := by group
        _ = t * k := by rw [h3]; group
    exact ⟨⟨k, hkK, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩, rfl⟩
  let e : ↥(K₁ ⊓ centralizer ({t} : Set G)) ≃*
      ↥(L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z))) :=
    MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hmap := pPrimeCore_map_iso 2 e
  have c1 : Nat.card ↥(pPrimeCoreOf 2 (K₁ ⊓ centralizer ({t} : Set G))) =
      Nat.card ↥(pPrimeCore 2 ↥(K₁ ⊓ centralizer ({t} : Set G))) := by
    unfold pPrimeCoreOf
    exact Subgroup.card_map_of_injective (K₁ ⊓ centralizer ({t} : Set G)).subtype_injective
  have c2 : Nat.card ↥(pPrimeCoreOf 2 (L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z)))) =
      Nat.card ↥(pPrimeCore 2 ↥(L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z)))) := by
    unfold pPrimeCoreOf
    exact Subgroup.card_map_of_injective (L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z))).subtype_injective
  rw [c1, c2, ← hmap]
  exact (Subgroup.card_map_of_injective e.injective).symm


omit [Finite G] in
theorem hasSL2Model_of_equiv' {A B : Type} [Group A] [Group B] (e : A ≃* B) {P : ℕ → Prop}
    (h : HasSL2Model B P) : HasSL2Model A P := by
  obtain ⟨F', iF, fF, hP, ⟨e'⟩⟩ := h
  exact ⟨F', iF, fF, hP, ⟨e.trans e'⟩⟩

theorem odd_card_OddCore (z : G) : Odd (Nat.card ↥(OddCore z)) := by
  have h1 : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
  have h2 : Nat.card ↥(OddCore z) = Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
    Subgroup.card_map_of_injective (Cen z).subtype_injective
  rw [h2]
  exact h1

omit [Finite G] in
theorem KA_of_inj {K : Subgroup G} (hKC : K ≤ Cen z)
    (hinj : Function.Injective ((toBar z).comp (Subgroup.inclusion hKC))) :
    ∀ x ∈ K, x ∈ OddCore z → x = 1 := by
  intro x hx hxA
  have h1 : toBar z ⟨x, hKC hx⟩ = 1 := by
    obtain ⟨c, hc, hcx⟩ := hxA
    have : c = ⟨x, hKC hx⟩ := Subtype.ext hcx
    rw [this] at hc
    rw [← ker_toBar] at hc
    exact hc
  have h2 : (⟨x, hx⟩ : ↥K) = 1 := hinj (by
    simp only [MonoidHom.comp_apply, map_one]
    exact h1)
  exact congrArg Subtype.val h2

theorem NFCtx.card_A_dvd_torus (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {t : G}
    (hg : GoodInvolution z S L₁ L₂ q t) :
    Nat.card ↥(OddCore z) ∣ (if q % 4 = 1 then q + 1 else q - 1) := by
  obtain ⟨-, hdvd⟩ := nf_embed h11 hF hMC hT h hg
  have hO := (h.outer_of_good hg).1.cyclic_card.2
  have h1 : Nat.card ↥(pPrimeCoreOf 2 (L₁ ⊓ centralizer ({toBar z ⟨t, h.SC hg.1⟩} : Set (CentralizerBar z)))) ∣
      Nat.card ↥(L₁ ⊓ centralizer ({toBar z ⟨t, h.SC hg.1⟩} : Set (CentralizerBar z))) :=
    Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)
  rw [hO] at h1
  exact hdvd.trans h1

theorem nf_KA
    (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) :
    (∀ x ∈ K₁, x ∈ OddCore z → x = 1) ∧ (∀ x ∈ K₂, x ∈ OddCore z → x = 1) := by
  by_cases hq9 : q = 9
  · subst hq9
    obtain ⟨t, hg⟩ := h.good
    have hdvd := h.card_A_dvd_torus h11 hF hMC hT hg
    have hodd := odd_card_OddCore z
    have hdvd10 : Nat.card ↥(OddCore z) ∣ 2 * 5 := by simpa using hdvd
    have hA5 : Nat.card ↥(OddCore z) ∣ 5 :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_left.2 hodd).symm (by simpa [mul_comm] using hdvd10)
    exact ⟨inf_oddCore_eq_one_q9 h.comp.le₁ h.comp.perf₁ h.comp.bar₁ (compData_central_of_toBar₁ h.comp)
        h.pair.sl₁ hA5,
      inf_oddCore_eq_one_q9 h.comp.le₂ (compData_perf₂ h.pair h.comp) h.comp.bar₂
        (compData_central_of_toBar₂ h.comp) h.pair.sl₂ hA5⟩
  · exact ⟨KA_of_inj h.comp.le₁ (compData_inj₁ h.pair h.comp hq9),
      KA_of_inj h.comp.le₂ (compData_inj₂ h.pair h.comp hq9)⟩


theorem nf_conc201
    (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hT : TypeCl z k S) (hTL : TypeL4 z k S ε q) (hnf : ¬ Fused ε q)
    (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) : Conc201 z k S M := by
  obtain ⟨hKA₁, hKA₂⟩ := nf_KA h11 hF hMC hT h
  obtain ⟨t, hg⟩ := h.good
  obtain ⟨hcyc, hdvd⟩ := nf_embed h11 hF hMC hT h hg
  obtain ⟨hne, hnsw, hLC, hconj, hn₁, hn₂⟩ := h.good_props hg
  have htC := h.SC hg.1
  have ht2 := sq_of_good hg
  have htN := h.nrm_K₁ hKA₁ hKA₂ htC ht2 hn₁
  have htr := h.card_O2_transport hKA₁ htC htN
  have hm₁ : HasSL2Model ↥K₁ (fun r => r = q) :=
    hasSL2Model_of_equiv' (exists_equiv_barOf h.comp.le₁ hKA₁).some (by rw [h.comp.bar₁]; exact h.pair.sl₁)
  have hm₂ : HasSL2Model ↥K₂ (fun r => r = q) :=
    hasSL2Model_of_equiv' (exists_equiv_barOf h.comp.le₂ hKA₂).some (by rw [h.comp.bar₂]; exact h.pair.sl₂)
  have htnot : t ∉ K₁ ⊔ K₂ := fun hmem => hLC (em_le_LC z (h.comp.layer ▸ hmem))
  subst hMC
  exact ⟨ε, q, hTL, rfl, K₁, K₂, ⟨h.comp.layer.symm, h.comp.comm, h.card_inf_two hKA₁ hKA₂⟩, hm₁, hm₂, hcyc,
    t, hconj, hg.1, htN, htr ▸ hdvd, ⟨fun hmem => absurd hmem htnot, fun hf => absurd hf hnf⟩⟩

theorem nonfused_false
    (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hTL : TypeL4 z k S ε q) (hnf : ¬ Fused ε q) : False := by
  have hctx : Stage2Ctx G z k S := hF.ctx.ctx17.ctx
  obtain ⟨hk, L₁, L₂, hL4⟩ := hTL
  have hTL' : TypeL4 z k S ε q := ⟨hk, L₁, L₂, hL4⟩
  subst hk
  have hT : TypeCl z (Kind.l4 ε) S := Or.inl ⟨ε, q, rfl, L₁, L₂, hL4⟩
  have hP := hL4.pair
  have h4a : pLayerOf 2 (Cen z) = Em (Cen z) := by
    have := hF.ctx.thm4.1
    rwa [hMC] at this
  obtain ⟨K₁, K₂, hK⟩ := exists_compData hP h4a
  rcases hL4.fusion with ⟨hf, -⟩ | ⟨-, x, hx, hgood, hfuse⟩
  · exact hnf hf
  · obtain ⟨y, hy, -⟩ := hgood
    exact hF.fail (nf_conc201 h11 hF hMC hT hTL' hnf ⟨hctx, hK, hL4, ⟨x, hx⟩, hfuse, ⟨y, hy⟩⟩)

end Final

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L7Theta
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L7Aux
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L6W
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Sev

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Bg
open CFSG.GH74.GLS.Stage2.Final.L26 (WBar_eq_map_O22Res)
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (IG_11_7)

section Helpers

theorem layer_centralizes_pPrimeCore (X : Type) [Group X] [Finite X] :
    ∀ y ∈ layer X, ∀ a ∈ pPrimeCore 2 X, y * a = a * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (pPrimeCore 2 X) :=
    CFSG.LocalAnalysis.ComponentInitial.isSolvable_pPrimeCore_two
  have hsub : (pPrimeCore 2 X).IsSubnormal := (pPrimeCore_normal (p := 2) (G := X)).isSubnormal
  have h := (CFSG.LocalCores.component_solvable_centralizer hsolv hsub).2
  intro y hy a ha
  have : y ∈ centralizer (pPrimeCore 2 X : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hy
  exact (mem_centralizer_iff.1 this a ha).symm

theorem commutator_centralizes {X : Type} [Group X] {A : Subgroup X} [A.Normal] {u : X}
    (hu : ∀ a ∈ A, u * a = a * u) (q : X) :
    ∀ a ∈ A, (u * q * u⁻¹ * q⁻¹) * a = a * (u * q * u⁻¹ * q⁻¹) := by
  intro a ha
  have ha' : q⁻¹ * a * q ∈ A := by
    have := (inferInstance : A.Normal).conj_mem a ha q⁻¹
    simpa using this
  have h1 : u⁻¹ * (q⁻¹ * a * q) = (q⁻¹ * a * q) * u⁻¹ := by
    have h2 := hu _ ha'
    calc u⁻¹ * (q⁻¹ * a * q) = u⁻¹ * ((q⁻¹ * a * q) * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * (q⁻¹ * a * q)) * u⁻¹ := by rw [h2]
      _ = (q⁻¹ * a * q) * u⁻¹ := by group
  have h3 : u * a * u⁻¹ = a := by
    have := hu a ha
    calc u * a * u⁻¹ = (a * u) * u⁻¹ := by rw [this]
      _ = a := by group
  calc (u * q * u⁻¹ * q⁻¹) * a = u * q * (u⁻¹ * (q⁻¹ * a * q)) * q⁻¹ := by group
    _ = u * q * ((q⁻¹ * a * q) * u⁻¹) * q⁻¹ := by rw [h1]
    _ = (u * a * u⁻¹) * (u * q * u⁻¹ * q⁻¹) := by group
    _ = a * (u * q * u⁻¹ * q⁻¹) := by rw [h3]

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem not_centralizes_of_fail (hF : Fail17 G z k S (Cen z))
    (hLE : pLayerOf 2 (Cen z) = Em (Cen z)) (Q : Sylow 2 ↥(Cen z))
    (hQ : (Q : Subgroup ↥(Cen z)).map (Cen z).subtype = S) :
    ¬ ∀ s ∈ (Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z), ∀ a ∈ pPrimeCore 2 ↥(Cen z),
      s * a = a * s := by
  intro h
  apply hF.fail
  refine ⟨hLE, fun h' => absurd h' (lt_irrefl _), fun _ => ?_⟩
  refine isInternalDirectProduct_of_sylow_of_centralizes ⟨Q, hQ⟩ ?_
  rintro s ⟨hsS, w, hw, rfl⟩ f ⟨f', hf', rfl⟩
  obtain ⟨q, hqQ, hqw⟩ := (hQ ▸ hsS : _ ∈ (Q : Subgroup ↥(Cen z)).map (Cen z).subtype)
  have hqw' : q = w := Subtype.ext hqw
  subst hqw'
  have := h q ⟨hqQ, hw⟩ f' hf'.2
  exact congrArg Subtype.val this

end Helpers

section Key

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem key_in_layer {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (ctx : Stage2Ctx G z k S) (hF : Fail17 G z k S (Cen z))
    (hLE : pLayerOf 2 (Cen z) = Em (Cen z)) (hEm : Em (Cen z) ≠ ⊥)
    (hsh : G2Shape z S r₁ 3 L₁ L₂) (hzE : z ∈ Em (Cen z))
    (Q : Sylow 2 ↥(Cen z)) (hQ : (Q : Subgroup ↥(Cen z)).map (Cen z).subtype = S)
    {u : ↥(Cen z)} (huQ : u ∈ (Q : Subgroup ↥(Cen z))) (hu2 : u ^ 2 = 1)
    (huA : ∀ a ∈ pPrimeCore 2 ↥(Cen z), u * a = a * u) : u ∈ layer ↥(Cen z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : orderOf z = 2 := ctx.central.1
  have hsh' : G2Shape z S r₁ 3 L₁ L₂ := hsh
  obtain ⟨hr₁, hr₂, hgt₁, hprod, m₁, m₂, -, h3, -, hrel, hind₁, hind₂⟩ := hsh
  obtain ⟨hWL, hzL₂, hinv₂⟩ := three_basic hsh'
  obtain ⟨hW8, hW4⟩ := WBar_card_pow_four hsh'
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
  have hno := not_centralizes_of_fail hF hLE Q hQ
  have hinf := inf_centralizer_eq hsh' hz Q hno
  have huS : (u : G) ∈ S := hQ ▸ ⟨u, huQ, rfl⟩
  have hcomm_W : ∀ w ∈ WBar z, toBar z u * w * (toBar z u)⁻¹ * w⁻¹ ∈
      centralizer (L₂ : Set (CentralizerBar z)) := by
    intro w hw
    rw [WBar_eq_map_O22Res] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    obtain ⟨q', hq'Q, hq'W, hq'⟩ := exists_lift Q hw₀
    rw [← hq']
    have hcQ : u * q' * u⁻¹ * q'⁻¹ ∈ (Q : Subgroup ↥(Cen z)) :=
      mul_mem (mul_mem (mul_mem huQ hq'Q) (inv_mem huQ)) (inv_mem hq'Q)
    have hcW : u * q' * u⁻¹ * q'⁻¹ ∈ O22Res ↥(Cen z) := by
      have : (O22Res ↥(Cen z)).Normal := O22Res_normal
      have h1 : u * q' * u⁻¹ ∈ O22Res ↥(Cen z) := this.conj_mem q' hq'W u
      exact mul_mem h1 (inv_mem hq'W)
    have hcC : u * q' * u⁻¹ * q'⁻¹ ∈ centralizer (pPrimeCore 2 ↥(Cen z) : Set ↥(Cen z)) :=
      mem_centralizer_iff.2 fun a ha => (commutator_centralizes huA q' a ha).symm
    have hc : u * q' * u⁻¹ * q'⁻¹ ∈ zpowers (zElt z) := by
      rw [← hinf]
      exact ⟨⟨hcQ, hcW⟩, hcC⟩
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hc
    have h1 : toBar z (u * q' * u⁻¹ * q'⁻¹) = (zBar z) ^ n := by
      rw [← hn, map_zpow]
      rfl
    simp only [map_mul, map_inv] at h1
    rw [h1]
    exact mem_centralizer_iff.2 fun g _ => ((Commute.zpow_right (show Commute g (zBar z) from
      zBar_central z g) n).eq)
  have hSC : S ≤ Cen z := ctx.S_le_Cen
  have hι : ∀ s : ↥S, toBar z (Subgroup.inclusion hSC s) ∈ L₂ ⊔ SBar S z := fun s =>
    mem_sup_right ⟨Subgroup.inclusion hSC s, Subgroup.mem_subgroupOf.2 s.2, rfl⟩
  let ι : ↥S →* ↥(L₂ ⊔ SBar S z) :=
    ((toBar z).comp (Subgroup.inclusion hSC)).codRestrict (L₂ ⊔ SBar S z) hι
  obtain ⟨Θ, hΘs, hΘone, hΘsign⟩ := exists_theta m₂ hind₂
  let φ : ↥S →* ℤˣ := Equiv.Perm.sign.comp (Θ.comp ι)
  have hR : (RC S z).subgroupOf S ≤ φ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    have hsL : ((s : S) : G) ∈ LC z := (Subgroup.mem_subgroupOf.1 hs).2
    have hbar : toBar z (Subgroup.inclusion hSC s) ∈ L₁ ⊔ L₂ := by
      rw [hprod.1]
      exact ⟨Subgroup.inclusion hSC s, Subgroup.mem_subgroupOf.2 hsL, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hprod.2.1 hbar
    have hac : a ∈ centralizer (L₂ : Set (CentralizerBar z)) :=
      mem_centralizer_iff.2 fun y hy => (hprod.2.1 a ha y hy).symm
    refine (hΘsign (ι s)).2 ⟨b, hb, a, hac, ?_⟩
    show toBar z (Subgroup.inclusion hSC s) = b * a
    rw [← hab]
    exact hprod.2.1 a ha b hb
  have hKtop : φ.ker ≠ ⊤ := by
    obtain ⟨sb, hsb, hnot⟩ := exists_outer_of_inducedPGL2 m₂ hind₂
    obtain ⟨x, hx, rfl⟩ := hsb
    intro htop
    have hxS : ((x : ↥(Cen z)) : G) ∈ S := Subgroup.mem_subgroupOf.1 hx
    have h1 : φ ⟨(x : G), hxS⟩ = 1 := by
      have : (⟨(x : G), hxS⟩ : ↥S) ∈ φ.ker := htop ▸ Subgroup.mem_top _
      exact this
    exact hnot ((hΘsign (ι ⟨(x : G), hxS⟩)).1 h1)
  have hRidx : ((RC S z).subgroupOf S).index = 2 := hrel
  have hker_idx : φ.ker.index = 2 := by
    have h1 : φ.ker.index ∣ ((RC S z).subgroupOf S).index := Subgroup.index_dvd_of_le hR
    rw [hRidx] at h1
    have h2 : φ.ker.index ≠ 1 := fun h => hKtop (Subgroup.index_eq_one.1 h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd h h2
    · exact h
  have hRK : (RC S z).subgroupOf S = φ.ker := by
    refine Subgroup.eq_of_le_of_card_ge hR ?_
    have h1 := φ.ker.index_mul_card
    have h2 := ((RC S z).subgroupOf S).index_mul_card
    rw [hker_idx] at h1
    rw [hRidx] at h2
    omega
  have hx : toBar z u ∈ L₂ ⊔ SBar S z := mem_sup_right ⟨u, Subgroup.mem_subgroupOf.2 huS, rfl⟩
  obtain ⟨w, hw, hwc⟩ := exists_mul_centralizer_of_commutes m₂ hind₂ hWL hW8 hW4 hx hcomm_W
  have huLC : (u : G) ∈ LC z := by
    have hsign : Equiv.Perm.sign (Θ ⟨toBar z u, hx⟩) = 1 :=
      (hΘsign ⟨toBar z u, hx⟩).2 ⟨w, hWL hw, w⁻¹ * toBar z u, hwc, by group⟩
    have hmem : (⟨(u : G), huS⟩ : ↥S) ∈ φ.ker := hsign
    rw [← hRK] at hmem
    exact (Subgroup.mem_subgroupOf.1 hmem).2
  have hūL : toBar z u ∈ L₁ ⊔ L₂ := by
    rw [hprod.1]
    exact ⟨u, Subgroup.mem_subgroupOf.2 huLC, rfl⟩
  have hc₀sup : w⁻¹ * toBar z u ∈ L₁ ⊔ L₂ :=
    mul_mem (inv_mem (mem_sup_right (hWL hw))) hūL
  have hc₀L₁ : w⁻¹ * toBar z u ∈ L₁ :=
    mem_left_of_centralizes hr₂ m₂ hprod.2.1 hprod.2.2 hc₀sup hwc
  obtain ⟨J, hJ⟩ := exists_component_of_Em_ne_bot hEm
  have hJL : J.map (toBar z) = L₁ :=
    comp_eq_L1_of_three hsh' (isComponent_map_pPrimeCore hJ)
  have hJlayer : J ≤ layer ↥(Cen z) := le_sSup hJ
  rw [← hJL] at hc₀L₁
  obtain ⟨j, hjJ, hj⟩ := hc₀L₁
  have hjA : ∀ a ∈ pPrimeCore 2 ↥(Cen z), j * a = a * j :=
    layer_centralizes_pPrimeCore _ j (hJlayer hjJ)
  obtain ⟨v, hv⟩ : ∃ v : ↥(Cen z), v = j⁻¹ * u := ⟨_, rfl⟩
  have hcomm_wc : w * (w⁻¹ * toBar z u) = (w⁻¹ * toBar z u) * w :=
    mem_centralizer_iff.1 hwc w (hWL hw)
  have hvbar : toBar z v = w := by
    rw [hv, map_mul, map_inv, hj]
    calc (w⁻¹ * toBar z u)⁻¹ * toBar z u
        = (w⁻¹ * toBar z u)⁻¹ * (w * (w⁻¹ * toBar z u)) := by group
      _ = (w⁻¹ * toBar z u)⁻¹ * ((w⁻¹ * toBar z u) * w) := by rw [hcomm_wc]
      _ = w := by group
  have hvW : v ∈ O22Res ↥(Cen z) := by
    have hwW : w ∈ (O22Res ↥(Cen z)).map (toBar z) := by
      rw [← WBar_eq_map_O22Res]
      exact hw
    obtain ⟨w', hw'W, hw'⟩ := hwW
    have hA1 : w'⁻¹ * v ∈ pPrimeCore 2 ↥(Cen z) := QuotientGroup.eq.1 (hw'.trans hvbar.symm)
    have hvw : v = w' * (w'⁻¹ * v) := by group
    rw [hvw]
    exact mul_mem hw'W (pPrimeCore_le_O22Res hA1)
  have hvA : ∀ a ∈ pPrimeCore 2 ↥(Cen z), v * a = a * v := by
    intro a ha
    have h1 : j⁻¹ * a = a * j⁻¹ := by
      have h2 := hjA a ha
      calc j⁻¹ * a = j⁻¹ * (a * j) * j⁻¹ := by group
        _ = j⁻¹ * (j * a) * j⁻¹ := by rw [h2]
        _ = a * j⁻¹ := by group
    rw [hv]
    calc j⁻¹ * u * a = j⁻¹ * (u * a) := by group
      _ = j⁻¹ * (a * u) := by rw [huA a ha]
      _ = (j⁻¹ * a) * u := by group
      _ = (a * j⁻¹) * u := by rw [h1]
      _ = a * (j⁻¹ * u) := by group
  obtain ⟨q', hq'Q, hq'W, hq'⟩ := exists_lift Q hvW
  have hna : v⁻¹ * q' ∈ pPrimeCore 2 ↥(Cen z) := QuotientGroup.eq.1 hq'.symm
  obtain ⟨kq, hkq⟩ := Q.isPGroup' ⟨q', hq'Q⟩
  have hq'C : ∀ x ∈ pPrimeCore 2 ↥(Cen z), q' * x = x * q' :=
    centralizes_of_mul_eq hodd ⟨kq, congrArg Subtype.val hkq⟩ hvA hna (by group)
  have hq'mem : q' ∈ zpowers (zElt z) := by
    rw [← hinf]
    exact ⟨⟨hq'Q, hq'W⟩, mem_centralizer_iff.2 fun a ha => (hq'C a ha).symm⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hq'mem
  have hzl : zElt z ∈ layer ↥(Cen z) := by
    rw [Em_eq] at hzE
    obtain ⟨y, hy, hyz⟩ := hzE
    have : y = zElt z := Subtype.ext hyz
    rw [← this]
    exact hy
  obtain ⟨a, ha⟩ : ∃ a : ↥(Cen z), a = q'⁻¹ * v := ⟨_, rfl⟩
  have haA : a ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [ha]
    exact QuotientGroup.eq.1 hq'
  have hu_eq : u = (j * zElt z ^ n) * a := by
    rw [hn, ha, hv]
    group
  have hj'layer : j * zElt z ^ n ∈ layer ↥(Cen z) :=
    mul_mem (hJlayer hjJ) (zpow_mem hzl n)
  have hcommj : Commute (j * zElt z ^ n) a :=
    layer_centralizes_pPrimeCore _ _ hj'layer a haA
  have hao : orderOf a ∣ Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := by
    have h1 : orderOf (⟨a, haA⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣ Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at h1
  obtain ⟨t, ht⟩ := Odd.of_dvd_nat hodd hao
  have h1 : u ^ orderOf a = u := by
    rw [ht, pow_succ, pow_mul, hu2, one_pow, one_mul]
  have hum : u = (j * zElt z ^ n) ^ orderOf a := by
    conv_lhs => rw [← h1, hu_eq]
    rw [hcommj.mul_pow, pow_orderOf_eq_one, mul_one]
  rw [hum]
  exact pow_mem hj'layer _

end Key

section Main

theorem lemma17_7B_of (h171 : Prop17_1) : Lemma17_7B := by
  intro G _ _ z k S M h hL hq u hu2 huD
  obtain ⟨hMC, hA1⟩ := h171 G z k S M h.ctx h.fail
  subst hMC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ctx : Stage2Ctx G z k S := h.ctx.ctx
  have hz : orderOf z = 2 := ctx.central.1
  have hLE : pLayerOf 2 (Cen z) = Em (Cen z) := pLayerOf_eq_Em_of_central hq
  have hEm : Em (Cen z) ≠ ⊥ := hLE ▸ hL
  obtain ⟨⟨hrk, hzE, -⟩, hb⟩ := lemma17_6_thm h171 G z k S (Cen z) h hEm
  obtain ⟨⟨r₁, L₁, L₂, hsh⟩, -⟩ := hb hLE
  have hcoat : IsCoatom (Cen z) := h.ctx.mem.1
  have hsimp : IsSimpleGroup G := (isKProperSimple_iff.1 ctx.std.kps).1
  have hDM : pPrimeCoreOf 2 (Cen z) ≤ Cen z := Subgroup.map_subtype_le _
  have hDn : ∀ m ∈ Cen z, ∀ d ∈ pPrimeCoreOf 2 (Cen z), m * d * m⁻¹ ∈ pPrimeCoreOf 2 (Cen z) :=
    fun m hm d hd => pPrimeCoreOf_norm hm hd
  have hNorm : normalizer (pPrimeCoreOf 2 (Cen z) : Set G) = Cen z :=
    normalizer_eq_of_coatom hcoat hA1 hDM hDn
  have huC : u ∈ Cen z := hNorm ▸ Subgroup.centralizer_le_normalizer _ huD
  obtain ⟨Q, hQ⟩ := ctx.sylow
  obtain ⟨uX, huX⟩ : ∃ uX : ↥(Cen z), uX = ⟨u, huC⟩ := ⟨_, rfl⟩
  have huXo : orderOf uX = 2 := by
    rw [← hu2, ← Subgroup.orderOf_coe, huX]
  have huX2 : uX ^ 2 = 1 := by
    have := pow_orderOf_eq_one uX
    rwa [huXo] at this
  have huXA : ∀ a ∈ pPrimeCore 2 ↥(Cen z), uX * a = a * uX := by
    intro a ha
    have h1 : ((a : ↥(Cen z)) : G) ∈ pPrimeCoreOf 2 (Cen z) := ⟨a, ha, rfl⟩
    apply Subtype.ext
    have := mem_centralizer_iff.1 huD _ h1
    rw [huX]
    exact this.symm
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow Q (x := uX) ⟨1, by rw [pow_one]; exact huX2⟩
  have hu'2 : (g * uX * g⁻¹) ^ 2 = 1 := by
    have : (g * uX * g⁻¹) ^ 2 = g * (uX * uX) * g⁻¹ := by
      rw [pow_two]
      group
    rw [this, ← pow_two, huX2]
    group
  have hu'A : ∀ a ∈ pPrimeCore 2 ↥(Cen z), (g * uX * g⁻¹) * a = a * (g * uX * g⁻¹) := by
    intro a ha
    have ha' : g⁻¹ * a * g ∈ pPrimeCore 2 ↥(Cen z) := by
      have := (pPrimeCore_normal (p := 2) (G := ↥(Cen z))).conj_mem a ha g⁻¹
      simpa using this
    have h1 := huXA _ ha'
    calc g * uX * g⁻¹ * a = g * (uX * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * uX) * g⁻¹ := by rw [h1]
      _ = a * (g * uX * g⁻¹) := by group
  have hkey := key_in_layer ctx h hLE hEm hsh hzE Q hQ hg hu'2 hu'A
  have hu'E : ((g * uX * g⁻¹ : ↥(Cen z)) : G) ∈ Em (Cen z) := by
    rw [Em_eq]
    exact ⟨_, hkey, rfl⟩
  have hu'o : orderOf ((g * uX * g⁻¹ : ↥(Cen z)) : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective uX
    simpa [huXo] using this
  have hcz : z * ((g * uX * g⁻¹ : ↥(Cen z)) : G) = ((g * uX * g⁻¹ : ↥(Cen z)) : G) * z :=
    (mem_centralizer_singleton_iff.1 (g * uX * g⁻¹).2).symm
  have hu'z : ((g * uX * g⁻¹ : ↥(Cen z)) : G) = z := by
    by_contra hne
    have := two_le_pRank_of_two_involutions hz hu'o (Ne.symm hne) hcz hzE hu'E
    omega
  have hu''z : g * uX * g⁻¹ = zElt z := Subtype.ext hu'z
  have hgz : zElt z * g = g * zElt z := Subtype.ext (mem_centralizer_singleton_iff.1 g.2).symm
  have hXz : uX = zElt z := by
    calc uX = g⁻¹ * (g * uX * g⁻¹) * g := by group
      _ = g⁻¹ * zElt z * g := by rw [hu''z]
      _ = g⁻¹ * (zElt z * g) := by group
      _ = g⁻¹ * (g * zElt z) := by rw [hgz]
      _ = zElt z := by group
  have := congrArg Subtype.val hXz
  rw [huX] at this
  exact this

end Main

theorem prop17_8_thm (h172 : Lemma17_2) (h171 : Prop17_1) (hAB : IG_11_7) : Prop17_8 :=
  prop17_8_of_leaves h172 h171 (lemma17_7B_of h171) hAB

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

module

public import CFSG.CGT.PushingUpLit.SolKR2.WeakF0Core
public import CFSG.CGT.PushingUpLit.SolKR2.WeakSigAlg
public import CFSG.CGT.PushingUpLit.SolKR2.Pair
public import CFSG.CGT.PushingUpLit.SolKR2.TorusData

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup IsTI BenderCenterInput
  UnitaryTwoGenerationInput)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

namespace FirstHalf

variable {G : Type} [Group G] [Finite G]

section DataLevel


variable {V : Subgroup G} {g α x : G} (D : Data31 V g α x) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include D hCen hU

theorem card_C : Nat.card ↥(conjSubgroup x V) = 16 := by
  rw [card_conjSubgroup]
  exact D.card_eq_sixteen hCen hU

theorem card_C₀ : Nat.card ↥(omegaOneSub (conjSubgroup x V)) = 4 := by
  rw [omegaOneSub_conj D.core.comm x, card_conjSubgroup]
  exact D.card_omega_four hCen hU

theorem card_dN_sixteen : Nat.card ↥(dN V x) = 16 := by
  rw [Inner.card_dN D hCen hU, D.card_omega_four hCen hU, card_C₀ D hCen hU]

theorem card_dS2_sixtyfour : Nat.card ↥(dS2 V x) = 64 := by
  have h := Inner.card_dS2 D hCen hU
  rw [card_C₀ D hCen hU, card_dN_sixteen D hCen hU, card_C D hCen hU] at h
  omega

theorem card_dS_sixteen : Nat.card ↥(dS V g x) = 16 := by
  rw [Inner.card_dS D hCen hU, card_C D hCen hU]

theorem C₀_le_dS : omegaOneSub (conjSubgroup x V) ≤ dS V g x := by
  rw [← Inner.inf_dN_dS D hCen hU]
  exact inf_le_right

theorem C_le_normalizer_dN : conjSubgroup x V ≤ Subgroup.normalizer (dN V x : Set G) :=
  fun _ hc => D.le_normalizer hCen hU (C_le_dX V x hc)

theorem cent_N_of_not_mem {s n : G} (hs : s ∈ dS2 V x) (hsN : s ∉ dN V x) (hn : n ∈ dN V x)
    (hsn : s * n = n * s) : n ∈ omegaOneSub (conjSubgroup x V) := by
  obtain ⟨n₁, hn₁, c, hc, rfl⟩ := exists_mul_of_mem_sup (C_le_normalizer_dN D hCen hU) hs
  have hcC₀ : c ∉ omegaOneSub (conjSubgroup x V) := fun hc0 =>
    hsN ((dN V x).mul_mem hn₁
      ((show omegaOneSub (conjSubgroup x V) ≤ dN V x from le_sup_right) hc0))
  refine Inner.cent_C D hCen hU hc hcC₀ hn ?_
  have h1 : n * n₁ = n₁ * n := Inner.N_comm D hCen hU hn hn₁
  calc c * n = n₁⁻¹ * (n₁ * c * n) := by group
    _ = n₁⁻¹ * (n * (n₁ * c)) := by rw [hsn]
    _ = n₁⁻¹ * (n * n₁) * c := by group
    _ = n * c := by rw [h1]; group

theorem mem_normalizer_dS2 {k : G} (hkN : k ∈ Subgroup.normalizer (dN V x : Set G))
    (hkC : k ∈ Subgroup.normalizer (conjSubgroup x V : Set G)) {s : G} (hs : s ∈ dS2 V x) :
    k * s * k⁻¹ ∈ dS2 V x := by
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup (C_le_normalizer_dN D hCen hU) hs
  have e : k * (n * c) * k⁻¹ = (k * n * k⁻¹) * (k * c * k⁻¹) := by group
  rw [e]
  exact (dS2 V x).mul_mem (dN_le_dS2 V x ((Subgroup.mem_normalizer_iff.mp hkN n).mp hn))
    (C_le_dS2 V x ((Subgroup.mem_normalizer_iff.mp hkC c).mp hc))

theorem mem_normalizer_dS {k : G} (hkN : k ∈ Subgroup.normalizer (dN V x : Set G))
    (hkC : k ∈ Subgroup.normalizer (conjSubgroup x V : Set G)) {s : G} (hs : s ∈ dS V g x) :
    k * s * k⁻¹ ∈ dS V g x := by
  have hSc : ∀ s ∈ dS V g x, ∀ t ∈ dS V g x, s * t = t * s :=
    fun s hs t ht => Inner.S_comm D hCen hU hs ht
  have hSsq : ∀ s ∈ dS V g x, s * s = 1 := fun s hs => Inner.S_sq D hCen hU hs
  have hinv : ∀ z ∈ conjSubgroup k (dS V g x), k⁻¹ * z * k ∈ dS V g x :=
    fun z hz => mem_conjSubgroup.mp hz
  have hE'S2 : conjSubgroup k (dS V g x) ≤ dS2 V x := fun z hz => by
    have := mem_normalizer_dS2 D hCen hU hkN hkC (dS_le_dS2 V g x (hinv z hz))
    rwa [show k * (k⁻¹ * z * k) * k⁻¹ = z by group] at this
  have hE'c : ∀ y ∈ conjSubgroup k (dS V g x), ∀ z ∈ conjSubgroup k (dS V g x), y * z = z * y :=
    fun y hy z hz => by
      have h1 := hSc _ (hinv y hy) _ (hinv z hz)
      calc y * z = k * ((k⁻¹ * y * k) * (k⁻¹ * z * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * z * k) * (k⁻¹ * y * k)) * k⁻¹ := by rw [h1]
        _ = z * y := by group
  have hE'2 : ∀ y ∈ conjSubgroup k (dS V g x), y * y = 1 := fun y hy => by
    have h1 := hSsq _ (hinv y hy)
    calc y * y = k * ((k⁻¹ * y * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hne : conjSubgroup k (dS V g x) ≠ dN V x := by
    intro heq
    have hSN : dS V g x ≤ dN V x := fun z hz => by
      have hz' : k * z * k⁻¹ ∈ conjSubgroup k (dS V g x) := by
        rw [mem_conjSubgroup, show k⁻¹ * (k * z * k⁻¹) * k = z by group]
        exact hz
      rw [heq] at hz'
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hkN) (k * z * k⁻¹)).mp hz'
      rwa [inv_inv, show k⁻¹ * (k * z * k⁻¹) * k = z by group] at this
    have h1 : dN V x ⊓ dS V g x = dS V g x := inf_of_le_right hSN
    rw [Inner.inf_dN_dS D hCen hU] at h1
    have h2 := card_dS_sixteen D hCen hU (g := g)
    rw [← h1, card_C₀ D hCen hU] at h2
    omega
  have key := e16_unique_generic (N := dN V x) (S₂ := dS2 V x) (S := dS V g x)
    (C₀ := omegaOneSub (conjSubgroup x V)) (E' := conjSubgroup k (dS V g x))
    (fun n hn => Inner.N_sq D hCen hU hn)
    (fun s hs => D.le_normalizer hCen hU (dS2_le_dX V x hs)) (card_dN_sixteen D hCen hU)
    (card_dS2_sixtyfour D hCen hU) (card_C₀ D hCen hU) (dS_le_dS2 V g x) hSsq
    (by rw [inf_comm]; exact Inner.inf_dN_dS D hCen hU) (card_dS_sixteen D hCen hU)
    (fun s hs hsN n hn hsn => cent_N_of_not_mem D hCen hU hs hsN hn hsn) (dN_le_dS2 V x)
    hE'S2 hE'c hE'2 (by rw [card_conjSubgroup]; exact card_dS_sixteen D hCen hU) hne
  have : k * s * k⁻¹ ∈ conjSubgroup k (dS V g x) := by
    rw [mem_conjSubgroup, show k⁻¹ * (k * s * k⁻¹) * k = s by group]
    exact hs
  rwa [key] at this

theorem comm_mem_dS {a k : G} (ha : a ∈ omegaOneSub (conjSubgroup g V)) (hkX : k ∈ dX V x)
    (hkN : k ∈ Subgroup.normalizer (dN V x : Set G))
    (hkC : k ∈ Subgroup.normalizer (conjSubgroup x V : Set G)) :
    a * k * a⁻¹ * k⁻¹ ∈ dS V g x := by
  obtain ⟨y, hy, hay⟩ := Inner.inner_mem_S D hCen hU ha
  have h1 := hay k hkX
  have h2 : k * y⁻¹ * k⁻¹ ∈ dS V g x :=
    mem_normalizer_dS D hCen hU hkN hkC ((dS V g x).inv_mem hy)
  have e : a * k * a⁻¹ * k⁻¹ = y * (k * y⁻¹ * k⁻¹) := by
    calc a * k * a⁻¹ * k⁻¹ = (a * k * a⁻¹) * k⁻¹ := rfl
      _ = (y * k * y⁻¹) * k⁻¹ := by rw [h1]
      _ = y * (k * y⁻¹ * k⁻¹) := by group
  rw [e]
  exact (dS V g x).mul_mem hy h2

theorem eq_one_of_comm_mem {a k : G} (ha : a ∈ omegaOneSub (conjSubgroup g V))
    (hkX : k ∈ dX V x) (hkN : k ∈ Subgroup.normalizer (dN V x : Set G))
    (hq : ∀ s ∈ conjSubgroup x V, k * s * k⁻¹ * s⁻¹ ∈ dN V x →
      s ∈ omegaOneSub (conjSubgroup x V))
    (hak : a * k * a⁻¹ * k⁻¹ ∈ dN V x) : a = 1 := by
  by_contra ha1
  obtain ⟨y, hy, hay⟩ := Inner.inner_mem_S D hCen hU ha
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup (C_le_normalizer_dN D hCen hU)
    (dS_le_dS2 V g x hy)
  have h1 : (n * c) * k * (n * c)⁻¹ * k⁻¹ ∈ dN V x := by
    have := hay k hkX
    rwa [this] at hak
  have hkn : k * n * k⁻¹ ∈ dN V x := (Subgroup.mem_normalizer_iff.mp hkN n).mp hn
  have h2 : c * k * c⁻¹ * k⁻¹ ∈ dN V x := by
    have e : c * k * c⁻¹ * k⁻¹ = n⁻¹ * ((n * c) * k * (n * c)⁻¹ * k⁻¹) * (k * n * k⁻¹) := by
      group
    rw [e]
    exact (dN V x).mul_mem ((dN V x).mul_mem ((dN V x).inv_mem hn) h1) hkn
  have h3 : k * c * k⁻¹ * c⁻¹ ∈ dN V x := by
    have e : k * c * k⁻¹ * c⁻¹ = (c * k * c⁻¹ * k⁻¹)⁻¹ := by group
    rw [e]
    exact (dN V x).inv_mem h2
  have hc0 := hq c hc h3
  have hcN : c ∈ dN V x := (show omegaOneSub (conjSubgroup x V) ≤ dN V x from le_sup_right) hc0
  have hyN : n * c ∈ dN V x := (dN V x).mul_mem hn hcN
  obtain ⟨β, hβ, hβ1⟩ := exists_U0_ne_one D
  have hβX : β ∈ dX V x := U_le_dX V x (omegaOneSub_le V hβ)
  have hβN : β ∈ dN V x := (show omegaOneSub V ≤ dN V x from le_sup_left) hβ
  have h4 := hay β hβX
  have h5 : n * c * β = β * (n * c) := Inner.N_comm D hCen hU hyN hβN
  refine D.core.not_comm ha ha1 hβ hβ1 ?_
  calc a * β = (a * β * a⁻¹) * a := by group
    _ = (n * c * β * (n * c)⁻¹) * a := by rw [h4]
    _ = β * a := by rw [h5]; group

theorem exists_act_D {a : G} (ha : a ∈ omegaOneSub (conjSubgroup g V)) :
    ∃ d ∈ omegaOneSub V, ∀ u ∈ conjSubgroup x V, a * u * a⁻¹ = d * u * d⁻¹ := by
  obtain ⟨y, hy, hay⟩ := Inner.inner_mem_S D hCen hU ha
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup (C_le_normalizer_dN D hCen hU)
    (dS_le_dS2 V g x hy)
  obtain ⟨d, hd, b, hb, rfl⟩ := (D.pairUC hCen hU).exists_mul hCen hU hn
  refine ⟨d, hd, fun u hu => ?_⟩
  have h1 := hay u (C_le_dX V x hu)
  have hbc : b * c ∈ conjSubgroup x V :=
    (conjSubgroup x V).mul_mem (omegaOneSub_le _ hb) hc
  have hcomm := D.core.comm_conj' x (b * c) hbc u hu
  rw [h1]
  calc d * b * c * u * (d * b * c)⁻¹ = d * ((b * c) * u * (b * c)⁻¹) * d⁻¹ := by group
    _ = d * u * d⁻¹ := by rw [hcomm]; group

theorem commutator_eq_C₀ :
    ⁅omegaOneSub (conjSubgroup g V), omegaOneSub V⁆ = omegaOneSub (conjSubgroup x V) := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha d hd =>
    D.comm_mem_C₀ hCen hU ha hd) fun z hz => ?_
  obtain ⟨c, hc, hcz⟩ := D.exists_comm_eq hCen hU D.mem D.ne_one hz
  obtain ⟨n, hn, s₁, hs₁, hcns⟩ := D.exists_eq_mul hCen hU
    (Subgroup.mem_sup_right hc : c ∈ dN V x ⊔ conjSubgroup x V)
  obtain ⟨d, hd, b, hb, hnd⟩ := (D.pairUC hCen hU).exists_mul hCen hU hn
  have hsα : s₁ * α * s₁⁻¹ = α := by
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hs₁).2 α D.mem
    calc s₁ * α * s₁⁻¹ = (α * s₁) * s₁⁻¹ := by rw [← this]
      _ = α := by group
  have hbα : b * α * b⁻¹ = α := by
    have := D.comm_C₀_A₀ hCen hU D.mem hb
    calc b * α * b⁻¹ = (α * b) * b⁻¹ := by rw [← this]
      _ = α := by group
  have e : z = (α * d * α⁻¹ * d⁻¹)⁻¹ := by
    rw [← hcz, hcns, hnd]
    calc d * b * s₁ * α * (d * b * s₁)⁻¹ * α⁻¹
        = d * (b * (s₁ * α * s₁⁻¹) * b⁻¹) * d⁻¹ * α⁻¹ := by group
      _ = d * (b * α * b⁻¹) * d⁻¹ * α⁻¹ := by rw [hsα]
      _ = d * α * d⁻¹ * α⁻¹ := by rw [hbα]
      _ = (α * d * α⁻¹ * d⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator D.mem hd)

end DataLevel

omit [Finite G] in
theorem comm_inv_mul_eq {a a' k t t' : G} (ht : t = a * k * a⁻¹ * k⁻¹)
    (ht' : t' = a' * k * a'⁻¹ * k⁻¹) (h1 : a' * t = t * a') (h2 : a' * t' = t' * a')
    (h3 : t * t' = t' * t) :
    (a'⁻¹ * a) * k * (a'⁻¹ * a)⁻¹ * k⁻¹ = t'⁻¹ * t := by
  have e1 : (a'⁻¹ * a) * k * (a'⁻¹ * a)⁻¹ * k⁻¹ = a'⁻¹ * t * (k * a' * k⁻¹) := by
    rw [ht]
    group
  have e2 : k * a' * k⁻¹ = t'⁻¹ * a' := by
    rw [ht']
    group
  have c1 : a'⁻¹ * t = t * a'⁻¹ := (Commute.inv_left (show Commute a' t from h1)).eq
  have c2 : a'⁻¹ * t'⁻¹ * a' = t'⁻¹ := by
    have h4 := (Commute.inv_right (show Commute a' t' from h2)).eq
    calc a'⁻¹ * t'⁻¹ * a' = a'⁻¹ * (t'⁻¹ * a') := by group
      _ = a'⁻¹ * (a' * t'⁻¹) := by rw [← h4]
      _ = t'⁻¹ := by group
  have c3 : t * t'⁻¹ = t'⁻¹ * t := (Commute.inv_right (show Commute t t' from h3)).eq
  rw [e1, e2, c1]
  calc t * a'⁻¹ * (t'⁻¹ * a') = t * (a'⁻¹ * t'⁻¹ * a') := by group
    _ = t * t'⁻¹ := by rw [c2]
    _ = t'⁻¹ * t := c3

omit [Finite G] in
theorem conj_mem_omegaOneSub {W : Subgroup G} (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k d : G}
    (hk : k ∈ Subgroup.normalizer (W : Set G)) (hd : d ∈ omegaOneSub W) :
    k * d * k⁻¹ ∈ omegaOneSub W := by
  rw [mem_omegaOneSub_iff hc] at hd ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hk d).mp hd.1, ?_⟩
  calc k * d * k⁻¹ * (k * d * k⁻¹) = k * (d * d) * k⁻¹ := by group
    _ = 1 := by rw [hd.2]; group

omit [Finite G] in
theorem omegaOne_C {M B V : Subgroup G} {x : G} (h : R2 M B)
    (hC : conjSubgroup x V = omegaTwoSub B) :
    omegaOneSub (conjSubgroup x V) = omegaOneSub B := by
  rw [hC, h.omegaOne_omegaTwo]

section R2Level


theorem A_ne_B0 {M B V : Subgroup G} {g α x : G} (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (h : R2 M B) (D : Data31 V g α x)
    (hC : conjSubgroup x V = omegaTwoSub B) :
    omegaOneSub (conjSubgroup g V) ≠ omegaOneSub B := by
  intro heq
  obtain ⟨β, hβ, hβ1⟩ := exists_U0_ne_one D
  have hα : α ∈ omegaOneSub (conjSubgroup x V) := by
    rw [omegaOne_C h hC, ← heq]
    exact D.mem
  have hαN : α ∈ dN V x := (show omegaOneSub (conjSubgroup x V) ≤ dN V x from le_sup_right) hα
  have hβN : β ∈ dN V x := (show omegaOneSub V ≤ dN V x from le_sup_left) hβ
  exact D.core.not_comm D.mem D.ne_one hβ hβ1 (Inner.N_comm D hCen hU hαN hβN)

theorem inf_A_centralizer {M B V : Subgroup G} {g α x : G} (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (hW : R2Weak) (h : R2 M B) (D : Data31 V g α x)
    (hC : conjSubgroup x V = omegaTwoSub B) (hA : omegaOneSub (conjSubgroup g V) ∈ Lam M B) :
    omegaOneSub (conjSubgroup g V) ⊓ Subgroup.centralizer (omegaTwoSub B : Set G) = ⊥ :=
  Pair.inf_centralizer_eq_bot hCen hU hW h hA (A_ne_B0 hCen hU h D hC)

theorem exists_act_A {M B V : Subgroup G} {g α x : G} (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (hW : R2Weak) (h : R2 M B) (D : Data31 V g α x)
    (hC : conjSubgroup x V = omegaTwoSub B) (hA : omegaOneSub (conjSubgroup g V) ∈ Lam M B)
    {d : G} (hd : d ∈ omegaOneSub V) :
    ∃ a ∈ omegaOneSub (conjSubgroup g V),
      ∀ u ∈ conjSubgroup x V, a * u * a⁻¹ = d * u * d⁻¹ := by
  classical
  have hex : ∀ a : ↥(omegaOneSub (conjSubgroup g V)), ∃ d ∈ omegaOneSub V,
      ∀ u ∈ conjSubgroup x V, (a : G) * u * (a : G)⁻¹ = d * u * d⁻¹ :=
    fun a => exists_act_D D hCen hU a.2
  choose f hfD hf using hex
  let F : ↥(omegaOneSub (conjSubgroup g V)) → ↥(omegaOneSub V) := fun a => ⟨f a, hfD a⟩
  have hinj : Function.Injective F := by
    intro a a' haa
    have hfa : f a = f a' := congrArg Subtype.val haa
    have hcen : (a : G)⁻¹ * a' ∈ Subgroup.centralizer (omegaTwoSub B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : u ∈ conjSubgroup x V := by rw [hC]; exact hu
      have e : (a : G) * u * (a : G)⁻¹ = a' * u * (a' : G)⁻¹ := by
        rw [hf a u hu', hf a' u hu', hfa]
      calc u * ((a : G)⁻¹ * a') = (a : G)⁻¹ * ((a : G) * u * (a : G)⁻¹) * a' := by group
        _ = (a : G)⁻¹ * (a' * u * (a' : G)⁻¹) * a' := by rw [e]
        _ = ((a : G)⁻¹ * a') * u := by group
    have hmem : (a : G)⁻¹ * a' ∈ omegaOneSub (conjSubgroup g V) ⊓
        Subgroup.centralizer (omegaTwoSub B : Set G) :=
      Subgroup.mem_inf.2 ⟨(omegaOneSub (conjSubgroup g V)).mul_mem
        ((omegaOneSub (conjSubgroup g V)).inv_mem a.2) a'.2, hcen⟩
    rw [inf_A_centralizer hCen hU hW h D hC hA, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem)
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (D.core.card_omega_conj g).ge
  obtain ⟨a, ha⟩ := hbij.2 ⟨d, hd⟩
  have hfa : f a = d := congrArg Subtype.val ha
  exact ⟨a, a.2, fun u hu => by rw [hf a u hu, hfa]⟩

theorem dS_eq_sup {M B V : Subgroup G} {g α x : G} (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (hW : R2Weak) (h : R2 M B) (D : Data31 V g α x)
    (hC : conjSubgroup x V = omegaTwoSub B) (hA : omegaOneSub (conjSubgroup g V) ∈ Lam M B) :
    dS V g x = omegaOneSub (conjSubgroup g V) ⊔ omegaOneSub (conjSubgroup x V) := by
  classical
  obtain ⟨K, hKX, hK3, hKV, hKC, -, -, -, hqC⟩ := D.exists_torus hCen hU
  obtain ⟨k, hkK, hk1⟩ : ∃ k ∈ K, k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : K = ⊥ := eq_bot_iff.2 fun k hk => Subgroup.mem_bot.2 (hcon k hk)
    rw [hbot, Subgroup.card_bot] at hK3
    omega
  have hkX : k ∈ dX V x := hKX hkK
  have hkN : k ∈ Subgroup.normalizer (dN V x : Set G) := D.le_normalizer hCen hU hkX
  have hkC : k ∈ Subgroup.normalizer (conjSubgroup x V : Set G) := hKC hkK
  have hkV : k ∈ Subgroup.normalizer (V : Set G) := hKV hkK
  have hNC : Subgroup.normalizer (conjSubgroup x V : Set G) = M := by
    rw [hC]
    exact R2.normalizer_U h
  have hkM : k ∈ M := by
    rw [← hNC]
    exact hkC
  have hnormC : ∀ z ∈ Subgroup.normalizer (conjSubgroup x V : Set G),
      ∀ w ∈ conjSubgroup x V, z * w * z⁻¹ ∈ conjSubgroup x V :=
    fun z hz w hw => (Subgroup.mem_normalizer_iff.mp hz w).mp hw
  have hT2 : ∀ a ∈ omegaOneSub (conjSubgroup g V), a * k * a⁻¹ * k⁻¹ ∈ dS V g x :=
    fun a ha => comm_mem_dS D hCen hU ha hkX hkN hkC
  have hT3 : ∀ a ∈ omegaOneSub (conjSubgroup g V), a * k * a⁻¹ * k⁻¹ ∈ dN V x → a = 1 :=
    fun a ha hak => eq_one_of_comm_mem D hCen hU ha hkX hkN (hqC k hkK hk1) hak
  have hP6 : ∀ a ∈ omegaOneSub (conjSubgroup g V), ∃ a' ∈ omegaOneSub (conjSubgroup g V),
      ∃ b ∈ omegaOneSub (conjSubgroup x V), k * a * k⁻¹ = a' * b := by
    intro a ha
    by_cases hAk : conjSubgroup k (omegaOneSub (conjSubgroup g V)) = omegaOneSub (conjSubgroup g V)
    · refine ⟨k * a * k⁻¹, ?_, 1, Subgroup.one_mem _, by group⟩
      rw [← hAk, mem_conjSubgroup, show k⁻¹ * (k * a * k⁻¹) * k = a by group]
      exact ha
    · obtain ⟨d, hd, hΦ⟩ := exists_act_D D hCen hU ha
      have hd' : k * d * k⁻¹ ∈ omegaOneSub V :=
        conj_mem_omegaOneSub D.core.comm hkV hd
      obtain ⟨a'', ha'', hΦ''⟩ := exists_act_A hCen hU hW h D hC hA hd'
      have hA'Lam : conjSubgroup k (omegaOneSub (conjSubgroup g V)) ∈ Lam M B :=
        Lam.conj_mem hA hkM
      have hcomm : ∀ f ∈ conjSubgroup k (omegaOneSub (conjSubgroup g V)),
          ∀ e ∈ omegaOneSub (conjSubgroup g V), f * e = e * f := by
        intro f hf e he
        have ha₁ : k⁻¹ * f * k ∈ omegaOneSub (conjSubgroup g V) := mem_conjSubgroup.mp hf
        have ht := hT2 _ ha₁
        have hc1 : e * (k⁻¹ * f * k * k * (k⁻¹ * f * k)⁻¹ * k⁻¹) =
            (k⁻¹ * f * k * k * (k⁻¹ * f * k)⁻¹ * k⁻¹) * e :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht).2 e he
        have hf2 : f = (k⁻¹ * f * k * k * (k⁻¹ * f * k)⁻¹ * k⁻¹)⁻¹ * (k⁻¹ * f * k) := by group
        have c2 := (Commute.inv_right (show Commute e _ from hc1)).eq
        have c3 : (k⁻¹ * f * k) * e = e * (k⁻¹ * f * k) :=
          Lam.comm_self h hA _ ha₁ e he
        generalize k⁻¹ * f * k * k * (k⁻¹ * f * k)⁻¹ * k⁻¹ = t at hc1 hf2 c2
        generalize k⁻¹ * f * k = a₁ at hf2 c3
        rw [hf2]
        calc t⁻¹ * a₁ * e = t⁻¹ * (a₁ * e) := by group
          _ = t⁻¹ * (e * a₁) := by rw [c3]
          _ = (t⁻¹ * e) * a₁ := by group
          _ = (e * t⁻¹) * a₁ := by rw [c2]
          _ = e * (t⁻¹ * a₁) := by group
      have hcen : (k * a * k⁻¹) * a''⁻¹ ∈ Subgroup.centralizer (omegaTwoSub B : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have hu' : u ∈ conjSubgroup x V := by rw [hC]; exact hu
        have ha''M : a'' ∈ M := Lam.le_M hA ha''
        have hu₁ : a''⁻¹ * u * a'' ∈ conjSubgroup x V := by
          have := hnormC a''⁻¹ (by rw [hNC]; exact M.inv_mem ha''M) u hu'
          rwa [inv_inv] at this
        have hu₂ : k⁻¹ * (a''⁻¹ * u * a'') * k ∈ conjSubgroup x V := by
          have := hnormC k⁻¹ (Subgroup.inv_mem _ hkC) _ hu₁
          rwa [inv_inv] at this
        have e1 := hΦ'' _ hu₁
        have e2 := hΦ _ hu₂
        have step : (k * a * k⁻¹ * a''⁻¹) * u * (k * a * k⁻¹ * a''⁻¹)⁻¹ = u := by
          calc (k * a * k⁻¹ * a''⁻¹) * u * (k * a * k⁻¹ * a''⁻¹)⁻¹
              = k * (a * (k⁻¹ * (a''⁻¹ * u * a'') * k) * a⁻¹) * k⁻¹ := by group
            _ = k * (d * (k⁻¹ * (a''⁻¹ * u * a'') * k) * d⁻¹) * k⁻¹ := by rw [e2]
            _ = (k * d * k⁻¹) * (a''⁻¹ * u * a'') * (k * d * k⁻¹)⁻¹ := by group
            _ = a'' * (a''⁻¹ * u * a'') * a''⁻¹ := e1.symm
            _ = u := by group
        calc u * (k * a * k⁻¹ * a''⁻¹) = ((k * a * k⁻¹ * a''⁻¹) * u * (k * a * k⁻¹ * a''⁻¹)⁻¹) *
              (k * a * k⁻¹ * a''⁻¹) := by rw [step]
          _ = (k * a * k⁻¹ * a''⁻¹) * u := by group
      have hfmem : k * a * k⁻¹ ∈ conjSubgroup k (omegaOneSub (conjSubgroup g V)) := by
        rw [mem_conjSubgroup, show k⁻¹ * (k * a * k⁻¹) * k = a by group]
        exact ha
      have hb := Pair.mul_mem_B0_of_commute hCen hU hW h hA'Lam hA hAk hcomm hfmem
        ((omegaOneSub (conjSubgroup g V)).inv_mem ha'') hcen
      have hb' : k * a * k⁻¹ * a''⁻¹ ∈ omegaOneSub (conjSubgroup x V) := by
        rw [omegaOne_C h hC]
        exact hb
      refine ⟨a'', ha'', _, hb', ?_⟩
      have hc4 := R2.comm_B0 h hA a'' ha'' _ hb
      calc k * a * k⁻¹ = (k * a * k⁻¹ * a''⁻¹) * a'' := by group
        _ = a'' * (k * a * k⁻¹ * a''⁻¹) := hc4.symm
  have hAcomm : ∀ z ∈ omegaOneSub (conjSubgroup x V), ∀ a ∈ omegaOneSub (conjSubgroup g V),
      z * a = a * z := fun z hz a ha => (D.comm_C₀_A₀ hCen hU ha hz).symm
  have hC₀N : omegaOneSub (conjSubgroup x V) ≤
      Subgroup.normalizer (omegaOneSub (conjSubgroup g V) : Set G) :=
    le_normalizer_of_comm hAcomm
  have hinf : omegaOneSub (conjSubgroup g V) ⊓ omegaOneSub (conjSubgroup x V) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzA, hzC⟩ := Subgroup.mem_inf.mp hz
    have hz' : z ∈ omegaOneSub (conjSubgroup g V) ⊓
        Subgroup.centralizer (omegaTwoSub B : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hzA, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have hu' : u ∈ conjSubgroup x V := by rw [hC]; exact hu
      exact D.core.comm_conj' x u hu' z (omegaOneSub_le _ hzC)
    rw [inf_A_centralizer hCen hU hW h D hC hA] at hz'
    exact hz'
  have hA₀card : Nat.card ↥(omegaOneSub (conjSubgroup g V)) = 4 := by
    rw [D.core.card_omega_conj g]
    exact D.card_omega_four hCen hU
  have hW16 : Nat.card ↥(omegaOneSub (conjSubgroup g V) ⊔ omegaOneSub (conjSubgroup x V)) =
      16 := by
    have := card_sup_mul_card_inf_of_normalizes hC₀N
    rw [hinf, Subgroup.card_bot, mul_one, hA₀card, card_C₀ D hCen hU] at this
    omega
  have hsurj : ∀ s ∈ dS V g x, ∃ a ∈ omegaOneSub (conjSubgroup g V),
      ∃ b ∈ omegaOneSub (conjSubgroup x V), s = (a * k * a⁻¹ * k⁻¹) * b := by
    let θ : ↥(omegaOneSub (conjSubgroup g V)) × ↥(omegaOneSub (conjSubgroup x V)) →
        ↥(dS V g x) := fun p =>
      ⟨((p.1 : G) * k * (p.1 : G)⁻¹ * k⁻¹) * (p.2 : G),
        (dS V g x).mul_mem (hT2 p.1 p.1.2) (C₀_le_dS D hCen hU p.2.2)⟩
    have hinj : Function.Injective θ := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hpp
      have hθ : (a * k * a⁻¹ * k⁻¹) * b = (a' * k * a'⁻¹ * k⁻¹) * b' := congrArg Subtype.val hpp
      have htS : a * k * a⁻¹ * k⁻¹ ∈ dS V g x := hT2 a ha
      have ht'S : a' * k * a'⁻¹ * k⁻¹ ∈ dS V g x := hT2 a' ha'
      have h1 : a' * (a * k * a⁻¹ * k⁻¹) = (a * k * a⁻¹ * k⁻¹) * a' :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp htS).2 a' ha'
      have h2 : a' * (a' * k * a'⁻¹ * k⁻¹) = (a' * k * a'⁻¹ * k⁻¹) * a' :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht'S).2 a' ha'
      have h3 : (a * k * a⁻¹ * k⁻¹) * (a' * k * a'⁻¹ * k⁻¹) =
          (a' * k * a'⁻¹ * k⁻¹) * (a * k * a⁻¹ * k⁻¹) := Inner.S_comm D hCen hU htS ht'S
      have hid := comm_inv_mul_eq (a := a) (a' := a') (k := k) rfl rfl h1 h2 h3
      have hbb : (a' * k * a'⁻¹ * k⁻¹)⁻¹ * (a * k * a⁻¹ * k⁻¹) = b' * b⁻¹ := by
        calc (a' * k * a'⁻¹ * k⁻¹)⁻¹ * (a * k * a⁻¹ * k⁻¹)
            = (a' * k * a'⁻¹ * k⁻¹)⁻¹ * ((a * k * a⁻¹ * k⁻¹) * b) * b⁻¹ := by group
          _ = (a' * k * a'⁻¹ * k⁻¹)⁻¹ * ((a' * k * a'⁻¹ * k⁻¹) * b') * b⁻¹ := by rw [hθ]
          _ = b' * b⁻¹ := by group
      have hbmem : b' * b⁻¹ ∈ omegaOneSub (conjSubgroup x V) :=
        (omegaOneSub (conjSubgroup x V)).mul_mem hb' ((omegaOneSub (conjSubgroup x V)).inv_mem hb)
      have hN : (a'⁻¹ * a) * k * (a'⁻¹ * a)⁻¹ * k⁻¹ ∈ dN V x := by
        rw [hid, hbb]
        exact (show omegaOneSub (conjSubgroup x V) ≤ dN V x from le_sup_right) hbmem
      have hamem : a'⁻¹ * a ∈ omegaOneSub (conjSubgroup g V) :=
        (omegaOneSub (conjSubgroup g V)).mul_mem ((omegaOneSub (conjSubgroup g V)).inv_mem ha') ha
      have haa : a' = a := inv_mul_eq_one.mp (hT3 _ hamem hN)
      subst haa
      have hbb' : b = b' := mul_left_cancel hθ
      subst hbb'
      rfl
    have hbij : Function.Bijective θ := by
      refine hinj.bijective_of_nat_card_le ?_
      rw [Nat.card_prod, hA₀card, card_C₀ D hCen hU, card_dS_sixteen D hCen hU]
    intro s hs
    obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨s, hs⟩
    exact ⟨a, a.2, b, b.2, (congrArg Subtype.val hab).symm⟩
  have hSle : dS V g x ≤ omegaOneSub (conjSubgroup g V) ⊔ omegaOneSub (conjSubgroup x V) := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hsurj s hs
    obtain ⟨a', ha', b', hb', hk⟩ := hP6 a ha
    have e : (a * k * a⁻¹ * k⁻¹) * b = a * (b'⁻¹ * a'⁻¹) * b := by
      calc (a * k * a⁻¹ * k⁻¹) * b = a * (k * a * k⁻¹)⁻¹ * b := by group
        _ = a * (a' * b')⁻¹ * b := by rw [hk]
        _ = a * (b'⁻¹ * a'⁻¹) * b := by rw [mul_inv_rev]
    rw [e]
    set W := omegaOneSub (conjSubgroup g V) ⊔ omegaOneSub (conjSubgroup x V) with hWdef
    exact W.mul_mem (W.mul_mem (Subgroup.mem_sup_left ha)
      (W.mul_mem (W.inv_mem (Subgroup.mem_sup_right hb')) (W.inv_mem (Subgroup.mem_sup_left ha'))))
      (Subgroup.mem_sup_right hb)
  exact Subgroup.eq_of_le_of_card_ge hSle
    (hW16.trans (card_dS_sixteen D hCen hU).symm).le

theorem A_le_dS {M B V : Subgroup G} {g α x : G} (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (hW : R2Weak) (h : R2 M B) (D : Data31 V g α x)
    (hC : conjSubgroup x V = omegaTwoSub B) (hA : omegaOneSub (conjSubgroup g V) ∈ Lam M B) :
    omegaOneSub (conjSubgroup g V) ≤ dS V g x :=
  le_sup_left.trans (dS_eq_sup hCen hU hW h D hC hA).ge

theorem commutator_eq_B0 {M B V : Subgroup G} {g α x : G} (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (h : R2 M B) (D : Data31 V g α x)
    (hC : conjSubgroup x V = omegaTwoSub B) :
    ⁅omegaOneSub (conjSubgroup g V), omegaOneSub V⁆ = omegaOneSub B :=
  (commutator_eq_C₀ D hCen hU).trans (omegaOne_C h hC)

theorem sup_eq_sup_U {M B V : Subgroup G} {g α x : G} (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (hW : R2Weak) (h : R2 M B) (D : Data31 V g α x)
    (hC : conjSubgroup x V = omegaTwoSub B) (hA : omegaOneSub (conjSubgroup g V) ∈ Lam M B) :
    omegaOneSub (conjSubgroup g V) ⊔ omegaOneSub V = omegaOneSub V ⊔ omegaTwoSub B := by
  have hS := dS_eq_sup hCen hU hW h D hC hA
  have hC₀ : omegaOneSub (conjSubgroup x V) ≤ omegaOneSub (conjSubgroup g V) ⊔ omegaOneSub V := by
    rw [← commutator_eq_C₀ D hCen hU]
    refine Subgroup.commutator_le.mpr fun a ha d hd => ?_
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right hd)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left ha)))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hd))
  rw [← hC]
  apply le_antisymm
  · refine sup_le ?_ le_sup_left
    have h1 : omegaOneSub (conjSubgroup g V) ≤ dS2 V x :=
      (A_le_dS hCen hU hW h D hC hA).trans (dS_le_dS2 V g x)
    exact h1.trans (sup_le (sup_le le_sup_left ((omegaOneSub_le _).trans le_sup_right))
      le_sup_right)
  · refine sup_le le_sup_right ?_
    calc conjSubgroup x V ≤ dS2 V x := C_le_dS2 V x
      _ = dN V x ⊔ dS V g x := Inner.dS2_eq_sup D hCen hU
      _ ≤ omegaOneSub (conjSubgroup g V) ⊔ omegaOneSub V :=
        sup_le (sup_le le_sup_right hC₀) (hS.le.trans (sup_le le_sup_left hC₀))

end R2Level

end FirstHalf

end CFSG.CGT.PushingUpLit.SolKR2

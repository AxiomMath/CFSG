module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Field
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Z4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem EndB.inf_centralizer_le_T (hs : Setting46e t L p f S w z V i j) {W : Subgroup X}
    (hWM : W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) (hW2 : IsPGroup 2 W)
    (hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W) :
    W ⊓ centralizer ({t} : Set X) ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT1 := hs.lemma45.isSylowOf_T
  have hTt : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({t} : Set X) :=
    hT1.le.trans inf_le_left
  have heq := hT1.eq_of_le (le_inf hTW hTt)
    (le_inf inf_le_right (inf_le_left.trans hWM)) (hW2.to_le inf_le_left)
  rw [heq]

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem psi_mem_four (hL : LLayer hs π) {W : Subgroup X}
    (hWM : W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (hW2 : IsPGroup 2 W) {a b : X} (haW : a ∈ W) (hbW : b ∈ W) (hab : a * b = b * a)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (haS : ((hL.rho (QuotientGroup.mk ⟨a, hWM haW⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∉
      PSL3Four.S)
    (hbS : ((hL.rho (QuotientGroup.mk ⟨b, hWM hbW⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∉
      PSL3Four.S)
    (habS : ((hL.rho (QuotientGroup.mk ⟨a, hWM haW⟩ * QuotientGroup.mk ⟨b, hWM hbW⟩) :
      PSL3Four.R) : Equiv.Perm (Fin 42)) ∉ PSL3Four.S) {g : X} (hgW : g ∈ W) :
    hL.psi (QuotientGroup.mk ⟨g, hWM hgW⟩) = 1 ∨
      hL.psi (QuotientGroup.mk ⟨g, hWM hgW⟩) = hL.psi (QuotientGroup.mk ⟨a, hWM haW⟩) ∨
      hL.psi (QuotientGroup.mk ⟨g, hWM hgW⟩) = hL.psi (QuotientGroup.mk ⟨b, hWM hbW⟩) ∨
      hL.psi (QuotientGroup.mk ⟨g, hWM hgW⟩) =
        hL.psi (QuotientGroup.mk ⟨a, hWM haW⟩) * hL.psi (QuotientGroup.mk ⟨b, hWM hbW⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := hL.psi.comp (barHom hWM) with hφ
  set A := φ ⟨a, haW⟩ with hA
  set B := φ ⟨b, hbW⟩ with hB
  have hφa : A = hL.psi (QuotientGroup.mk ⟨a, hWM haW⟩) := rfl
  have hφb : B = hL.psi (QuotientGroup.mk ⟨b, hWM hbW⟩) := rfl
  have hφg : φ ⟨g, hgW⟩ = hL.psi (QuotientGroup.mk ⟨g, hWM hgW⟩) := rfl
  have hψ1 : ∀ g, hL.psi g = 1 ↔ ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) ∈
      PSL3Four.S := fun g => by rw [← MonoidHom.mem_ker, hL.mem_ker_psi, hL.rho_mem_S_iff]
  have hA1 : A ≠ 1 := fun h => haS ((hψ1 _).mp (hφa ▸ h))
  have hB1 : B ≠ 1 := fun h => hbS ((hψ1 _).mp (hφb ▸ h))
  have hAB1 : A * B ≠ 1 := by
    intro h
    apply habS
    rw [← hψ1, map_mul, ← hφa, ← hφb]
    exact h
  have hA2 : A ^ 2 = 1 := by
    rw [hA, ← map_pow]
    have : (⟨a, haW⟩ : ↥W) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ha2, Subgroup.coe_one])
    rw [this, map_one]
  have hB2 : B ^ 2 = 1 := by
    rw [hB, ← map_pow]
    have : (⟨b, hbW⟩ : ↥W) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hb2, Subgroup.coe_one])
    rw [this, map_one]
  have hABc : A * B = B * A := by
    rw [hA, hB, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hab
  have hK : Nat.card ↥(zpowers A) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hA2 hA1]
  have hn : ∀ k ∈ zpowers A, B * k * B⁻¹ ∈ zpowers A := by
    rintro _ ⟨n, rfl⟩
    have hBA : B * A * B⁻¹ = A := by rw [← hABc]; group
    change B * A ^ n * B⁻¹ ∈ zpowers A
    rw [← conj_zpow, hBA]
    exact zpow_mem (mem_zpowers A) n
  have hBK : B ∉ zpowers A := by
    intro h
    rcases EndB.eq_one_or_eq_of_mem_zpowers_sq hA2 h with h | h
    · exact hB1 h
    · apply hAB1
      rw [h, ← sq, hA2]
  have hcard := EndB.card_sup_zpowers hn (by rw [hB2]; exact one_mem _) hBK
  rw [hK] at hcard
  have hle' : zpowers A ⊔ zpowers B ≤ φ.range :=
    sup_le (zpowers_le.mpr ⟨_, rfl⟩) (zpowers_le.mpr ⟨_, rfl⟩)
  have hle : Nat.card φ.range ≤ 4 := by
    have hdvd := Subgroup.card_subgroup_dvd_card φ.range
    rw [← Subgroup.index, index_SR] at hdvd
    have hp : IsPGroup 2 φ.range := hW2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk] at hdvd ⊢
    have hk3 : k ≤ 2 := by
      by_contra hk3
      have : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 4 := by norm_num
  have heq : zpowers A ⊔ zpowers B = φ.range :=
    Subgroup.eq_of_le_of_card_ge hle' (by omega)
  have hmem : φ ⟨g, hgW⟩ ∈ closure ({A, B} : Set _) := by
    rw [show ({A, B} : Set _) = {A} ∪ {B} by rw [Set.insert_eq], Subgroup.closure_union,
      ← zpowers_eq_closure, ← zpowers_eq_closure, heq]
    exact ⟨_, rfl⟩
  rw [← hφg, ← hφa, ← hφb]
  exact mem_closure_pair hA2 hB2 hABc hmem

theorem rho_conj_of_psi_eq
    (hL : LLayer hs π) {g₁ g₂ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg₁ : g₁ ^ 2 = 1)
    (hg₂ : g₂ ^ 2 = 1) (hψ : hL.psi g₁ = hL.psi g₂)
    (hS : ((hL.rho g₂ : PSL3Four.R) : Equiv.Perm (Fin 42)) ∉ PSL3Four.S)
    {r d : Equiv.Perm (Fin 42)} (hd : d ∈ PSL3Four.R)
    (hrd : ((hL.rho g₂ : PSL3Four.R) : Equiv.Perm (Fin 42)) = d * r * d⁻¹) :
    ∃ d' ∈ PSL3Four.R, ((hL.rho g₁ : PSL3Four.R) : Equiv.Perm (Fin 42)) = d' * r * d'⁻¹ := by
  have h1 : hL.psi (g₂⁻¹ * g₁) = 1 := by rw [map_mul, map_inv, hψ, inv_mul_cancel]
  have hS' : ((hL.rho (g₂⁻¹ * g₁) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∈ PSL3Four.S :=
    (hL.rho_mem_S_iff _).mpr ((hL.mem_ker_psi _).mp h1)
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hS'
  have hsq : ∀ g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j), g ^ 2 = 1 →
      ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) * (hL.rho g : PSL3Four.R) = 1 := by
    intro g hg
    rw [← Subgroup.coe_mul, ← map_mul, ← sq, hg, map_one, Subgroup.coe_one]
  have h21 : ((hL.rho g₂ : PSL3Four.R) : Equiv.Perm (Fin 42)) ≠ 1 :=
    fun h => hS (by rw [h]; exact one_mem _)
  have h11 : ((hL.rho g₁ : PSL3Four.R) : Equiv.Perm (Fin 42)) ≠ 1 := by
    intro h
    rw [h, mul_one] at hS'
    exact hS (by simpa using inv_mem hS')
  obtain ⟨y, hyS, hy⟩ := CatFactsL4U4.conj_of_mul_mem_S (hL.rho g₂).2 (hL.rho g₁).2
    (hsq g₂ hg₂) (hsq g₁ hg₁) h21 h11 hS'
  refine ⟨y * d, mul_mem (PSL3Four.S_le_R hyS) hd, ?_⟩
  rw [← hy, hrd]
  group

theorem psi_eq_t_of_conj
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hQE : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) (g : X)
    (hτM : g * t * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (hτW : g * t * g⁻¹ ∈ W) {R₀ : Subgroup X}
    (hR₀ : R₀ ≤ centralizer ({g * t * g⁻¹} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (hR₀2 : IsPGroup 2 R₀)
    (h64 : 64 ≤ Nat.card R₀) :
    hL.psi (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩) = hL.psi (hs.setup.tBar i j) := by
  obtain ⟨x, hxD, hx2, hxM, h0, h1⟩ := hL.exists_x hZ
  have hWM := hW.le
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hs.beta.lt.le.trans hUW
  have htW : t ∈ W := hTW (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hxW : x ∈ W := hTW (mem_sup_left (mem_sup_right hxD))
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer (mem_inf.mp hxD).2)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hτ2' : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
    group
  have hτ2 := EndB.mk_sq hτM hτ2'
  obtain ⟨-, hrtS⟩ := hL.rho_t_facts
  have htb : hs.setup.tBar i j = (QuotientGroup.mk ⟨t, htM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := rfl
  have hexcl : ∀ {d : Equiv.Perm (Fin 42)}, d ∈ PSL3Four.R →
      (((hL.rho (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) =
        d * PSL3Four.r₃ * d⁻¹ ∨
      ((hL.rho (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) =
        d * PSL3Four.r₄ * d⁻¹) → False := by
    intro d hd h
    rcases h with h | h
    · exact hL.false_of_graph_conj hFC hKC hI hKF hZ hτM ⟨d, hd, h⟩
    · have := hL.card_le_32_of_unitary_X hUC hQE hτM hτ2' hd h hR₀ hR₀2
      omega
  have hxb2 := EndB.mk_sq hxM hx2
  have hxbt : (QuotientGroup.mk ⟨x, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
      hs.setup.tBar i j = hs.setup.tBar i j * QuotientGroup.mk ⟨x, hxM⟩ :=
    EndB.mk_comm hxM htM hxt
  have hxtb2 : ((QuotientGroup.mk ⟨x, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
      hs.setup.tBar i j) ^ 2 = 1 := by
    rw [(show Commute _ _ from hxbt).mul_pow, hxb2, hs.tBar_sq, one_mul]
  rcases hL.psi_mem_four hWM hW.isPGroup hxW htW hxt hx2 ht2 h0 hrtS h1 hτW with h | h | h | h
  · exact absurd ((hL.mem_ker_psi _).mp h) (fun hE => hL.false_of_conj_inner hZ hQc g hτM hE)
  · exfalso
    rcases hL.graph_unitary hxb2 hxbt h0 h1 with ⟨⟨d, hd, hdg⟩, -⟩ | ⟨⟨d, hd, hdu⟩, -⟩
    · obtain ⟨d', hd', h'⟩ := hL.rho_conj_of_psi_eq hτ2 hxb2 h h0 hd hdg
      exact hexcl hd' (Or.inl h')
    · obtain ⟨d', hd', h'⟩ := hL.rho_conj_of_psi_eq hτ2 hxb2 h h0 hd hdu
      exact hexcl hd' (Or.inr h')
  · exact h
  · exfalso
    have h' : hL.psi (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩) =
        hL.psi (QuotientGroup.mk ⟨x, hxM⟩ * hs.setup.tBar i j) := by
      rw [map_mul]
      exact h
    rcases hL.graph_unitary hxb2 hxbt h0 h1 with ⟨-, ⟨d, hd, hdu⟩⟩ | ⟨-, ⟨d, hd, hdg⟩⟩
    · obtain ⟨d', hd', h''⟩ := hL.rho_conj_of_psi_eq hτ2 hxtb2 h' h1 hd hdu
      exact hexcl hd' (Or.inr h'')
    · obtain ⟨d', hd', h''⟩ := hL.rho_conj_of_psi_eq hτ2 hxtb2 h' h1 hd hdg
      exact hexcl hd' (Or.inl h'')

theorem exists_conj_field_coset (hFF : L34FieldSylowFusionFact)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2)
    (hQE : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) {τ : X}
    (hτW : τ ∈ W) (hτ2 : τ ^ 2 = 1)
    (hψ : hL.psi (QuotientGroup.mk ⟨τ, hW.le hτW⟩) = hL.psi (hs.setup.tBar i j)) :
    ∃ q ∈ W, ∃ b : X, (b = 1 ∨ b = w ^ (orderOf w / 2) * t ^ i * z ^ j ∨ b = z ∨
      b = w ^ (orderOf w / 2) * t ^ i * z ^ j * z) ∧ q * τ * q⁻¹ = b * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWM := hW.le
  have hW2 := hW.isPGroup
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hs.beta.lt.le.trans hUW
  have htW : t ∈ W := hTW (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := inferInstance
  set Wb := barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W with hWb
  set P := Wb ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hP
  set τb := (QuotientGroup.mk ⟨τ, hWM hτW⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hτb
  have htbW : hs.setup.tBar i j ∈ Wb := mk_mem_barOf htM htW
  have hτbW : τb ∈ Wb := mk_mem_barOf (hWM hτW) hτW
  have hpE : τb * (hs.setup.tBar i j)⁻¹ ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    have h1 : hL.psi (τb * (hs.setup.tBar i j)⁻¹) = 1 := by
      rw [map_mul, map_inv, hψ, mul_inv_cancel]
    have := (hL.mem_ker_psi _).mp h1
    rwa [sup_of_le_left hQE] at this
  have hpP : τb * (hs.setup.tBar i j)⁻¹ ∈ P := mem_inf.mpr ⟨mul_mem hτbW (inv_mem htbW), hpE⟩
  have hWbS := isSylowOf_barOf hW
  have hPE := hWbS.inf_of_le_normalizer (le_top :
    layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤ ⊤) (fun x _ => by
      rw [mem_normalizer_iff]
      intro e
      refine ⟨fun he => hn.conj_mem e he x, fun he => ?_⟩
      have := hn.conj_mem _ he x⁻¹
      rwa [show x⁻¹ * (x * e * x⁻¹) * x⁻¹⁻¹ = e by group] at this)
  obtain ⟨Q₀, hQ₀⟩ := hPE.exists_sylow_eq_subgroupOf
  have htN : hs.setup.tBar i j ∈
      normalizer (P : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact mem_inf.mpr ⟨mul_mem (mul_mem htbW (mem_inf.mp hk).1) (inv_mem htbW),
        hn.conj_mem _ (mem_inf.mp hk).2 _⟩
    · intro hk
      have hk' : k = (hs.setup.tBar i j)⁻¹ * (hs.setup.tBar i j * k * (hs.setup.tBar i j)⁻¹) *
          (hs.setup.tBar i j)⁻¹⁻¹ := by group
      rw [hk']
      exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem htbW) (mem_inf.mp hk).1)
        (inv_mem (inv_mem htbW)), hn.conj_mem _ (mem_inf.mp hk).2 _⟩
  have hZP : (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype ≤ P :=
    le_inf (hL.center_le_pCore.trans (EndB.pCore_le_barOf hW)) (map_subtype_le _)
  have hcard : Nat.card ↥(P ⊓ GrSLit.zStarIn
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2 := by
    rw [zStarIn_eq, inf_of_le_right hZP, Subgroup.card_map_of_injective (subtype_injective _), h2]
  have hps : τb * (hs.setup.tBar i j)⁻¹ * hs.setup.tBar i j *
      (τb * (hs.setup.tBar i j)⁻¹ * hs.setup.tBar i j) = 1 := by
    rw [inv_mul_cancel_right, ← sq]
    exact EndB.mk_sq _ hτ2
  obtain ⟨q', hq'P, y₁, hy₁P, hy₁c, hy₁t, hq'τ⟩ := hFF (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) P (hs.setup.tBar i j)
    (Subgroup.isPerfect_iff.mp hL.isPerfect) hL.isL34Type hL.isL34Field ⟨inf_le_right, Q₀, hQ₀⟩
    htN hcard _ hpP hps
  rw [inv_mul_cancel_right] at hq'τ
  obtain ⟨y', hyW, hyeq⟩ := mem_barOf.mp (mem_inf.mp hy₁P).1
  have hyM : (y' : X) ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := y'.2
  have hymk : (QuotientGroup.mk ⟨(y' : X), hyM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      y₁ := hyeq
  have hyt : (y' : X) * t = t * y' := by
    refine mk_injOn hWM hW2 (mul_mem hyW htW) (mul_mem htW hyW) ?_
    have e1 : (QuotientGroup.mk ⟨(y' : X) * t, hWM (mul_mem hyW htW)⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = y₁ * hs.setup.tBar i j := by
      rw [← hymk, Standing.Setup42.tBar, ← QuotientGroup.mk_mul]
      rfl
    have e2 : (QuotientGroup.mk ⟨t * (y' : X), hWM (mul_mem htW hyW)⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = hs.setup.tBar i j * y₁ := by
      rw [← hymk, Standing.Setup42.tBar, ← QuotientGroup.mk_mul]
      rfl
    rw [e1, e2, hy₁t]
  have hyT : (y' : X) ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
    EndB.inf_centralizer_le_T hs hWM hW2 hTW
      (mem_inf.mpr ⟨hyW, mem_centralizer_singleton_iff.mpr hyt⟩)
  have hyE : (QuotientGroup.mk ⟨(y' : X), hyM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [hymk]
    exact (mem_inf.mp hy₁P).2
  have hyB := hL.mem_T_layer hFC hKC hZ hyT hyM hyE
  have hDsW : S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤ W :=
    fun d hd => hTW (mem_sup_left (mem_sup_right (mem_inf.mp hd).1))
  have hDsM : S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
      centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    fun d hd => K_le_centralizer_beta i j (mem_inf.mp hd).2
  have hyc : ∀ e ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      (y' : X) * e = e * y' := by
    intro e he
    have heE : (QuotientGroup.mk ⟨e, hDsM he⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
      hs.KBar_le_layer ⟨⟨e, hDsM he⟩, (mem_inf.mp he).2, rfl⟩
    have heP : (QuotientGroup.mk ⟨e, hDsM he⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ P :=
      mem_inf.mpr ⟨mk_mem_barOf (hDsM he) (hDsW he), heE⟩
    have h1 := hy₁c _ heP
    refine mk_injOn hWM hW2 (mul_mem hyW (hDsW he)) (mul_mem (hDsW he) hyW) ?_
    have e1 : (QuotientGroup.mk ⟨(y' : X) * e, hWM (mul_mem hyW (hDsW he))⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = y₁ * QuotientGroup.mk ⟨e, hDsM he⟩ := by
      rw [← hymk, ← QuotientGroup.mk_mul]
      rfl
    have e2 : (QuotientGroup.mk ⟨e * (y' : X), hWM (mul_mem (hDsW he) hyW)⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = QuotientGroup.mk ⟨e, hDsM he⟩ * y₁ := by
      rw [← hymk, ← QuotientGroup.mk_mul]
      rfl
    rw [e1, e2, h1]
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 :=
    hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hβn : ∀ k ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      (w ^ (orderOf w / 2) * t ^ i * z ^ j) * k * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ ∈
        S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
    intro k hk
    rw [(mem_centralizer_singleton_iff.mp (hDsM hk)).symm, mul_inv_cancel_right]
    exact hk
  obtain ⟨q₀, hqW, hqeq⟩ := mem_barOf.mp (mem_inf.mp hq'P).1
  have hqM : (q₀ : X) ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := q₀.2
  refine ⟨q₀, hqW, y', ?_, ?_⟩
  · rcases (EndB.mem_sup_zpowers_iff hβn (by rw [hβ2]; exact one_mem _)).mp hyB with h | h
    · rcases EndB.eq_of_comm_Dstar hFC hKC hs h hyc with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
    · have hc : ∀ e ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
          (y' : X) * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ * e =
            e * ((y' : X) * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹) := by
        intro e he
        have hβe : (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ * e =
            e * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ := by
          have := (mem_centralizer_singleton_iff.mp (hDsM he)).symm
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, this, mul_assoc, mul_inv_cancel, mul_one]
        rw [mul_assoc, hβe, ← mul_assoc, hyc e he, mul_assoc]
      rcases EndB.eq_of_comm_Dstar hFC hKC hs h hc with h' | h'
      · right; left
        rw [mul_inv_eq_one] at h'
        exact h'
      · right; right; right
        rw [mul_inv_eq_iff_eq_mul] at h'
        rw [h', (mem_centralizer_singleton_iff.mp (K_le_centralizer_beta i j
          hs.lemma45.z_mem.2)).symm]
  · refine mk_injOn hWM hW2 (mul_mem (mul_mem hqW hτW) (inv_mem hqW)) (mul_mem hyW htW) ?_
    have e1 : (QuotientGroup.mk ⟨(q₀ : X) * τ * (q₀ : X)⁻¹,
        hWM (mul_mem (mul_mem hqW hτW) (inv_mem hqW))⟩ :
          MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = q' * τb * q'⁻¹ := by
      rw [← hqeq, hτb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
    have e2 : (QuotientGroup.mk ⟨(y' : X) * t, hWM (mul_mem hyW htW)⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = y₁ * hs.setup.tBar i j := by
      rw [← hymk, Standing.Setup42.tBar, ← QuotientGroup.mk_mul]
      rfl
    rw [e1, e2, hq'τ]

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit

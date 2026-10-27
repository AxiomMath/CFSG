module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchNu
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1CornerDet
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1CornerTransfer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzCorner

@[expose] def omegaTwo {G : Type*} [Group G] {V : Subgroup G}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) : Subgroup G where
  carrier := {x | x ∈ V ∧ x ^ 4 = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    exact ⟨mul_mem hx hy, by rw [(Commute.mul_pow (hcomm x hx y hy) 4), hx1, hy1, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow 4⟩
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    exact ⟨inv_mem hx, by rw [inv_pow, hx1, inv_one]⟩

theorem mem_omegaTwo {G : Type*} [Group G] {V : Subgroup G}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) {x : G} :
    x ∈ omegaTwo hcomm ↔ x ∈ V ∧ x ^ 4 = 1 := Iff.rfl

end SzCorner

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

theorem comm_of_mem_V₁ (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) {x : G} (hx : x ∈ U₁) : x * w = w * x := by
  have hcomm := h.V₁_comm hμ hlam
  have hle : U₁ ≤ centralizer ({w} : Set G) := by
    rw [hlam]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp (mem_inf.mp hw).2 y hy
    · rw [mem_centralizer_singleton_iff]
      exact (hcomm w hw y hy).symm
  exact mem_centralizer_singleton_iff.mp (hle hx)

theorem conj_mem_V₁_of_normalizer (h : SzC1Stage G L f a t T d V U U₁ k)
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {n : G}
    (hn : n ∈ normalizer (U : Set G)) {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    n * w * n⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := by
  refine mem_inf.mpr ⟨h.conj_mem_U₁_of_normalizer hμ hn (mem_inf.mp hw).1,
    mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : n⁻¹ * y * n⁻¹⁻¹ ∈ U₁ :=
    h.conj_mem_U₁_of_normalizer hμ (inv_mem hn) (h.T₁_le_U₁ hy)
  have e := h.comm_of_mem_V₁ hμ hlam hw hy'
  rw [inv_inv] at e
  calc y * (n * w * n⁻¹) = n * ((n⁻¹ * y * n) * w) * n⁻¹ := by group
    _ = n * (w * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
    _ = n * w * n⁻¹ * y := by group

theorem comm_t_pow_eq (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    (w * t * w⁻¹ * t⁻¹) ^ 2 ^ k = w ^ 2 ^ (k + 1) := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, -⟩ := h.coords
  have hK' := h.card_K hK hc
  have hk := h.one_le_k hK hc
  set φ := (w * t) ^ 2 with hφ
  have hφA : φ ∈ szA₁ (szT₁ L T) := h.sq_mul_t_mem_szA₁ hK hc hμ (mem_inf.mp hw).1
  have hφ2 : φ ^ 2 = 1 := hc.sq_eq_one_of_mem_szA₁ h.ha hK' hφA
  have hφV₁ : φ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := h.V_le_V₁ (h.le hφA)
  have hcomm := h.V₁_comm hμ hlam
  have e1 : t * w * t⁻¹ = w⁻¹ * φ := by
    rw [hφ, h.sq_mul_t]
    group
  have e2 : w * t * w⁻¹ * t⁻¹ = w ^ 2 * φ⁻¹ := by
    have hφw : φ⁻¹ * w = w * φ⁻¹ := hcomm _ (inv_mem hφV₁) w hw
    calc w * t * w⁻¹ * t⁻¹ = w * (t * w * t⁻¹)⁻¹ := by group
      _ = w * (w⁻¹ * φ)⁻¹ := by rw [e1]
      _ = w * (φ⁻¹ * w) := by group
      _ = w * (w * φ⁻¹) := by rw [hφw]
      _ = w ^ 2 * φ⁻¹ := by rw [sq, mul_assoc]
  have hφk : φ ^ 2 ^ k = 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ', pow_mul, hφ2, one_pow]
  rw [e2, Commute.mul_pow (hcomm _ (pow_mem hw 2) _ (inv_mem hφV₁)), ← pow_mul, ← pow_succ',
    inv_pow, hφk, inv_one, mul_one]

theorem exists_pow_eq_of_mem_szA₁ (h : SzC1Stage G L f a t T d V U U₁ k)
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {b : G}
    (hb : b ∈ szA₁ (szT₁ L T)) :
    ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), w ^ 2 ^ (k + 1) = b := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, hκ⟩ := h.coords
  have hK' := h.card_K hK hc
  obtain ⟨w, hw, hwS⟩ := h.S_surj_V₁ hK hc hκ hlam (v b)
  refine ⟨w, hw, ?_⟩
  have hwA : w ^ 2 ^ (k + 1) ∈ szA₁ (szT₁ L T) := by
    rw [← h.comm_t_pow_eq hμ hlam hw]
    exact h.pow_mem_szA₁ (h.comm_t_mem (h.U₁_le (mem_inf.mp hw).1))
  rw [h.comm_t_pow_eq hμ hlam hw] at hwS
  exact hc.inj _ (szA₁_le _ hwA) _ (szA₁_le _ hb)
    (by rw [hc.u_eq_zero_of_mem_szA₁ h.ha hK' hwA, hc.u_eq_zero_of_mem_szA₁ h.ha hK' hb]) hwS

theorem conj_ne_of_not_centralizes
    (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {x : G}
    (hxN : x ∈ normalizer (U : Set G)) (hx2 : x ^ 2 = 1) {b : G} (hb : b ∈ szA₁ (szT₁ L T))
    (hxb : x * b * x⁻¹ ≠ b) (g : G) : g * t * g⁻¹ ≠ x := by
  intro hgx
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, -⟩ := h.coords
  have hK' := h.card_K hK hc
  have hk := h.one_le_k hK hc
  obtain ⟨w, hw, hwb⟩ := h.exists_pow_eq_of_mem_szA₁ hμ hlam hb
  have hxw := h.conj_mem_V₁_of_normalizer hμ hlam hxN hw
  have hcomm := h.V₁_comm hμ hlam
  have hxx : x * x = 1 := by rw [← sq]; exact hx2
  set z := w * (x * w * x⁻¹) with hz
  have hzV₁ : z ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := mul_mem hw hxw
  have hxz : x * z = z * x := by
    have e : x * z * x⁻¹ = z := by
      calc x * z * x⁻¹ = (x * w * x⁻¹) * ((x * x) * w * (x * x)⁻¹) := by rw [hz]; group
        _ = (x * w * x⁻¹) * w := by rw [hxx]; group
        _ = z := by rw [hz]; exact hcomm _ hxw _ hw
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [e]
  have hzC : z ∈ centralizer ({g * t * g⁻¹} : Set G) := by
    rw [mem_centralizer_singleton_iff, hgx]
    exact hxz.symm
  have hzU : z ∈ U := h.U₁_le (mem_inf.mp hzV₁).1
  obtain ⟨n, hn⟩ := h.isPGroup_U ⟨z, hzU⟩
  have hzn : z ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hz4 := h.pow_four_eq_one_of_mem_centralizer_conj g hzC hzn
  have hb2 : b ^ 2 = 1 := hc.sq_eq_one_of_mem_szA₁ h.ha hK' hb
  have hzpow : z ^ 2 ^ (k + 1) = b * (x * b * x⁻¹) := by
    rw [hz, Commute.mul_pow (hcomm _ hw _ hxw), conj_pow, hwb]
  have hz1 : z ^ 2 ^ (k + 1) = 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 ^ (j + 1 + 1) = 4 * 2 ^ j by ring, pow_mul, hz4, one_pow]
  rw [hzpow] at hz1
  apply hxb
  calc x * b * x⁻¹ = b⁻¹ * (b * (x * b * x⁻¹)) := by group
    _ = b⁻¹ := by rw [hz1, mul_one]
    _ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)

theorem conj_mul_t_mem_U₁
    (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hA : ∀ n ∈ normalizer (U : Set G), n ^ 2 = 1 →
      (∀ b ∈ szA₁ (szT₁ L T), n * b * n⁻¹ = b) → n ∈ U)
    (g : G) (hg : g * t * g⁻¹ ∈ normalizer (U : Set G)) : g * t * g⁻¹ * t ∈ U₁ := by
  have hx2 : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, h.t_sq]; group
  have hxU : g * t * g⁻¹ ∈ U := by
    refine hA _ hg hx2 fun b hb => ?_
    by_contra hxb
    exact h.conj_ne_of_not_centralizes hμ hlam hg hx2 hb hxb g rfl
  exact (h.mem_or_mul_t_mem hxU).resolve_left (h.conj_not_mem_U₁ g)

theorem exists_det_ker (h : SzC1Stage G L f a t T d V U U₁ k) (hf : f = 3)
    (hμ : U₁ ≤ centralizer (V : Set G)) :
    ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
      (K.subgroupOf (normalizer (U : Set G))).Normal ∧
      ⁅normalizer (U : Set G), normalizer (U : Set G)⁆ ≤ K ∧ U₁ ≤ K ∧ t ∉ K := by
  obtain ⟨Kf, _, _, _, u, v, κ, hK, hc, -⟩ := h.coords
  have hK' := h.card_K hK hc
  have hk := h.one_le_k hK hc
  have hA8 : Nat.card (szA₁ (szT₁ L T)) = 8 := by rw [h.card_szA₁ hK hc, hf]; norm_num
  set W := SzCorner.omegaTwo h.comm with hWdef
  have hmemW : ∀ x, x ∈ W ↔ x ∈ V ∧ x ^ 4 = 1 := fun x => SzCorner.mem_omegaTwo h.comm
  have hWV : W ≤ V := fun x hx => ((hmemW x).mp hx).1
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => h.comm x (hWV hx) y (hWV hy)
  have hW4 : ∀ x ∈ W, x ^ 4 = 1 := fun x hx => ((hmemW x).mp hx).2
  have hAW : szA₁ (szT₁ L T) ≤ W := fun b hb =>
    (hmemW b).mpr ⟨h.le hb, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      hc.sq_eq_one_of_mem_szA₁ h.ha hK' hb, one_pow]⟩
  have hsq : ∀ b ∈ szA₁ (szT₁ L T), ∃ r ∈ W, r ^ 2 = b := by
    intro b hb
    obtain ⟨x, hx, hxb⟩ := SzC1.exists_pow_eq_of_mem h.comm h.omega h.pow
      (by rw [h.card_szA₁ hK hc, h.card]) hb
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨x ^ 2 ^ j, (hmemW _).mpr ⟨pow_mem hx _, ?_⟩, ?_⟩
    · rw [← pow_mul, show 2 ^ j * 4 = 2 ^ (j + 1 + 1) by ring]
      exact h.pow x hx
    · rw [← pow_mul, ← pow_succ]
      exact hxb
  have hcardW : Nat.card W = 64 := by
    refine le_antisymm ?_ ?_
    · have := SzC1.card_le_of_pow_eq_one (A := szA₁ (szT₁ L T)) 2 W hWcomm
        (fun x hx hx2 => h.omega x (hWV hx) hx2) (fun x hx => hW4 x hx)
      rw [hA8] at this
      simpa using this
    · let φ : W →* G := MonoidHom.mk' (fun x => (x : G) ^ 2) fun x y => by
        rw [Subgroup.coe_mul]
        exact Commute.mul_pow (hWcomm x x.2 y y.2) 2
      have hcardφ := SzC1.card_eq_card_ker_mul_card_range φ
      have hker : 8 ≤ Nat.card φ.ker := by
        rw [← hA8]
        refine Nat.card_le_card_of_injective
          (fun b => (⟨⟨b, hAW b.2⟩, MonoidHom.mem_ker.mpr
            (hc.sq_eq_one_of_mem_szA₁ h.ha hK' b.2)⟩ : φ.ker)) ?_
        intro b b' hbb'
        exact Subtype.ext (by simpa using congrArg (fun z : φ.ker => ((z : W) : G)) hbb')
      have hrange : 8 ≤ Nat.card φ.range := by
        rw [← hA8]
        refine Nat.card_le_card_of_injective
          (fun b => (⟨b, by
            obtain ⟨r, hr, hrb⟩ := hsq b b.2
            exact ⟨⟨r, hr⟩, hrb⟩⟩ : φ.range)) ?_
        intro b b' hbb'
        exact Subtype.ext (by simpa using congrArg (fun z : φ.range => (z : G)) hbb')
      rw [hcardφ]
      nlinarith
  have h2 : ∀ x ∈ W, x ^ 2 = 1 → ∃ y ∈ W, x = y ^ 2 := by
    intro x hx hx2
    obtain ⟨r, hr, hrx⟩ := hsq x (h.omega x (hWV hx) hx2)
    exact ⟨r, hr, hrx.symm⟩
  have hH : normalizer (U : Set G) ≤ normalizer (W : Set G) := by
    intro n hn
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
    have hnV := h.normalizer_U_le_normalizer_V hn
    refine (hmemW _).mpr ⟨?_, ?_⟩
    · simpa using (mem_normalizer_iff.mp (inv_mem hnV) x).mp (hWV hx)
    · rw [show n⁻¹ * x * n = n⁻¹ * x * n⁻¹⁻¹ by rw [inv_inv], conj_pow, hW4 x hx]
      group
  obtain ⟨K, hKN, hKn, hab, hcen, hinv⟩ :=
    SzCorner.exists_ker_of_inv hWcomm hW4 hcardW h2 hH
  refine ⟨K, hKN, hKn, hab, fun x hx => ?_, ?_⟩
  · refine hcen x (le_normalizer (h.U₁_le hx)) fun w hw => ?_
    have e := mem_centralizer_iff.mp (hμ hx) w (hWV hw)
    rw [← e, mul_inv_cancel_right]
  · exact hinv t (le_normalizer h.t_mem_U) fun w hw => h.inv w (hWV hw)

end SzC1Stage

end CFSG.SeitzReduction.RankOne

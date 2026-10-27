module

public import CFSG.LargeExtraspecial.AS35CS63E
public import CFSG.LargeExtraspecial.FS65Wall
public import CFSG.LargeExtraspecial.AS35CS63F
public import CFSG.LargeExtraspecial.AS35CS63Res

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S63

namespace Six

variable {G : Type} [Group G] [Finite G] {S : Setting G} (K : Six S)

theorem conjCent_subset_gen (hn : 3 ≤ S.width) :
    Timmesfeld.CorB.conjCent K.zeta ⊆ (K.Hbar : Set (Cbar K.t)) := by
  rintro τ ⟨hτc, hτ⟩
  obtain ⟨c, rfl⟩ := K.exists_of_isConj hτ
  have hyM := K.lift_mem_M hτc
  by_cases hyz : (c : G) * S.z * (c : G)⁻¹ = S.z
  · have : c * K.zC * c⁻¹ = K.zC := Subtype.ext hyz
    rw [this]
    exact K.mem_Hbar_of (z_mem_Hhat K.htQ K.ht2)
  · exact K.mem_Hbar_of ((K.pair c hyM hyz).x_mem_Hhat_gen hn)

theorem commutator_conjCent_gen (hn : 3 ≤ S.width) {a b : Cbar K.t}
    (ha : a ∈ Timmesfeld.CorB.conjCent K.zeta) (hb : b ∈ Timmesfeld.CorB.conjCent K.zeta) :
    a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = K.zeta := by
  obtain ⟨a', ha', rfl⟩ := K.conjCent_subset_gen hn ha
  obtain ⟨b', hb', rfl⟩ := K.conjCent_subset_gen hn hb
  rw [SetLike.mem_coe, mem_subgroupOf] at ha' hb'
  have e : piC K.t a' * piC K.t b' * (piC K.t a')⁻¹ * (piC K.t b')⁻¹ =
      piC K.t (a' * b' * a'⁻¹ * b'⁻¹) := by simp only [map_mul, map_inv]
  rw [e]
  rcases (mem_Z2_iff K.htQ K.ht2).mp (commutator_mem_Z2_of_mem_Hhat ha' hb') with h | h | h | h
  · left
    rw [(piC_eq_one_iff K.ht2).mpr (Or.inl h)]
  · right
    rw [zeta]
    exact congrArg (piC K.t) (Subtype.ext h)
  · left
    rw [(piC_eq_one_iff K.ht2).mpr (Or.inr h)]
  · right
    rw [zeta, piC_eq_iff K.ht2]
    right
    change S.z = _ * K.t
    rw [show (↑(a' * b' * a'⁻¹ * b'⁻¹) : G) = S.z * K.t from h, mul_assoc, K.ht2, mul_one]

theorem exists_fusion_gen (hn : 3 ≤ S.width) {τ : Cbar K.t}
    (hτ : τ ∈ Timmesfeld.CorB.conjCent K.zeta) (hne : τ ≠ K.zeta) :
    ∃ f : centralizer ({K.t} : Set G), (f : G) ∈ S.QG ∧
      piC K.t f * K.zeta * (piC K.t f)⁻¹ = K.zeta ∧ piC K.t f * τ * (piC K.t f)⁻¹ = K.zeta * τ := by
  obtain ⟨c, rfl⟩ := K.exists_of_isConj hτ.2
  have hyM := K.lift_mem_M hτ.1
  have hyz : (c : G) * S.z * (c : G)⁻¹ ≠ S.z := fun h => hne (by
    rw [zeta]
    exact congrArg (piC K.t) (Subtype.ext h))
  set P := K.pair c hyM hyz with hP
  obtain ⟨c₀, hc₀Q, hc₀t, h₀⟩ := P.exists_conj_eq_gen hn
  refine ⟨⟨c₀, mem_centralizer_singleton_iff.mpr hc₀t⟩, hc₀Q, ?_, ?_⟩
  · rw [zeta, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    change c₀ * S.z * c₀⁻¹ = S.z
    rw [S.z_comm_QG hc₀Q]
    group
  · rw [zeta, ← map_inv, ← map_mul, ← map_mul, ← map_mul, piC_eq_iff K.ht2]
    right
    change S.z * ((c : G) * S.z * (c : G)⁻¹) = c₀ * ((c : G) * S.z * (c : G)⁻¹) * c₀⁻¹ * K.t
    have h1 : c₀ * ((c : G) * S.z * (c : G)⁻¹) * c₀⁻¹ = K.t * S.z * P.x := h₀
    rw [h1, ← K.pair_x c hyM hyz, ← hP]
    have htz : K.t * S.z = S.z * K.t := S.z_comm_QG K.htQ
    have htx : K.t * P.x = P.x * K.t := P.t_comm_x
    calc S.z * P.x = (K.t * K.t) * S.z * P.x := by rw [K.ht2, one_mul]
      _ = K.t * (K.t * S.z) * P.x := by group
      _ = K.t * (S.z * K.t) * P.x := by rw [htz]
      _ = K.t * S.z * (K.t * P.x) := by group
      _ = K.t * S.z * (P.x * K.t) := by rw [htx]
      _ = K.t * S.z * P.x * K.t := by group

theorem setup_gen (hn : 3 ≤ S.width) : Timmesfeld.CorB.Setup K.zeta where
  orderOf_eq := K.orderOf_zeta
  isPGroup := K.isPGroup_Hbar.to_le ((closure_le _).mpr (K.conjCent_subset_gen hn))
  class_two := by
    have hle : Timmesfeld.CorB.weakClosure K.zeta ≤ K.Hbar :=
      (closure_le _).mpr (K.conjCent_subset_gen hn)
    rw [eq_bot_iff, ← K.commutator_commutator_Hbar]
    exact commutator_mono (commutator_mono hle hle) hle
  fusion := fun τ hτc hτ hne => by
    obtain ⟨f, -, -, hf⟩ := K.exists_fusion_gen hn ⟨hτc, hτ⟩ hne
    exact hτ.trans (isConj_iff.mpr ⟨_, hf⟩)

theorem exists_conjCent_ne_gen (hn : 3 ≤ S.width) {h : G}
    (hxM : h * S.z * h⁻¹ ∈ S.M) (hxz : h * S.z * h⁻¹ ≠ S.z) (hta : K.t ∈ S.Qa h) :
    ∃ τ ∈ Timmesfeld.CorB.conjCent K.zeta, τ ≠ K.zeta := by
  set P : Pair S := ⟨h, K.t, K.hW, hxM, hxz, K.htQ, hta, K.ht1⟩ with hP
  obtain ⟨c', -, hc't, hc'⟩ := P.exists_conj_z_eq_gen hn
  set c : centralizer ({K.t} : Set G) := ⟨c', mem_centralizer_singleton_iff.mpr hc't⟩ with hc
  have hcz : (c * K.zC * c⁻¹ : centralizer ({K.t} : Set G)) = (K.t * P.x * S.z : G) := hc'
  have htx : K.t * P.x = P.x * K.t := P.t_comm_x
  have hxz' : P.x * S.z = S.z * P.x := P.x_comm_z
  have htz : K.t * S.z = S.z * K.t := S.z_comm_QG K.htQ
  refine ⟨piC K.t (c * K.zC * c⁻¹), ⟨?_, ?_⟩, ?_⟩
  · rw [zeta, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    change ((c * K.zC * c⁻¹ : centralizer ({K.t} : Set G)) : G) * S.z =
      S.z * ((c * K.zC * c⁻¹ : centralizer ({K.t} : Set G)) : G)
    rw [hcz]
    calc K.t * P.x * S.z * S.z = K.t * (P.x * S.z) * S.z := by group
      _ = K.t * (S.z * P.x) * S.z := by rw [hxz']
      _ = (K.t * S.z) * P.x * S.z := by group
      _ = S.z * (K.t * P.x * S.z) := by rw [htz]; group
  · exact isConj_iff.mpr ⟨piC K.t c, by rw [zeta, ← map_inv, ← map_mul, ← map_mul]⟩
  · rw [zeta, Ne, piC_eq_iff K.ht2]
    change ¬ (S.z = ((c * K.zC * c⁻¹ : centralizer ({K.t} : Set G)) : G) ∨
      S.z = ((c * K.zC * c⁻¹ : centralizer ({K.t} : Set G)) : G) * K.t)
    rw [hcz]
    rintro (h1 | h1)
    · have h2 : K.t * P.x = 1 := by
        have := congrArg (· * S.z⁻¹) h1
        simpa using this.symm
      have h3 : P.x = K.t := by
        calc P.x = K.t⁻¹ * (K.t * P.x) := by group
          _ = K.t := by rw [h2, mul_one, inv_eq_of_mul_eq_one_right K.ht2]
      exact P.x_not_mem_QG (h3 ▸ K.htQ)
    · have h2 : P.x = 1 := by
        have h4 : K.t * P.x * S.z * K.t = P.x * S.z := by
          calc K.t * P.x * S.z * K.t = K.t * (P.x * S.z) * K.t := by group
            _ = K.t * (S.z * P.x) * K.t := by rw [hxz']
            _ = (K.t * S.z) * (P.x * K.t) := by group
            _ = (S.z * K.t) * (K.t * P.x) := by rw [htz, htx]
            _ = S.z * (K.t * K.t) * P.x := by group
            _ = P.x * S.z := by rw [K.ht2, mul_one, hxz']
        rw [h4] at h1
        have := congrArg (· * S.z⁻¹) h1
        simpa using this.symm
      apply S.z_ne_one
      have h5 : P.x = h * S.z * h⁻¹ := rfl
      calc S.z = h⁻¹ * (h * S.z * h⁻¹) * h := by group
        _ = 1 := by rw [← h5, h2]; group

theorem conj_mem_E_gen (hn : 3 ≤ S.width) {τ : Cbar K.t}
    (hτ : IsConj K.zeta τ) (hτc : τ * K.zeta = K.zeta * τ) :
    τ ∈ K.Fbar ⊔ centralizer (K.Fbar : Set (Cbar K.t)) := by
  obtain ⟨c, rfl⟩ := K.exists_of_isConj hτ
  have hyM := K.lift_mem_M hτc
  by_cases hyz : (c : G) * S.z * (c : G)⁻¹ = S.z
  · have : c * K.zC * c⁻¹ = K.zC := Subtype.ext hyz
    rw [this]
    exact mem_sup_left K.zeta_mem_Fbar
  · have hyH := (K.pair c hyM hyz).x_mem_Hhat_gen hn
    obtain ⟨f, hfQ, hft0, hf0⟩ := exists_inner_of_mem_Hhat hyH
    have hft : f * K.t = K.t * f := hft0
    have hf : ∀ e ∈ S.QG, e * K.t = K.t * e →
        (f⁻¹ * ((c : G) * S.z * (c : G)⁻¹)) * e * (f⁻¹ * ((c : G) * S.z * (c : G)⁻¹))⁻¹ * e⁻¹ = 1 ∨
        (f⁻¹ * ((c : G) * S.z * (c : G)⁻¹)) * e * (f⁻¹ * ((c : G) * S.z * (c : G)⁻¹))⁻¹ * e⁻¹ =
          K.t := hf0
    set fC : centralizer ({K.t} : Set G) := ⟨f, mem_centralizer_singleton_iff.mpr hft⟩ with hfC
    have hy : c * K.zC * c⁻¹ = fC * (fC⁻¹ * (c * K.zC * c⁻¹)) := by group
    rw [hy, map_mul]
    refine mul_mem (mem_sup_left (K.mem_Fbar_of hfQ)) (mem_sup_right ?_)
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨e, he, rfl⟩ := K.exists_of_mem_Fbar hx
    rw [← map_mul, ← map_mul, piC_eq_iff K.ht2]
    have h := hf (e : G) he (mem_centralizer_singleton_iff.mp e.2)
    change f⁻¹ * ((c : G) * S.z * (c : G)⁻¹) * e = e * (f⁻¹ * ((c : G) * S.z * (c : G)⁻¹)) ∨
      f⁻¹ * ((c : G) * S.z * (c : G)⁻¹) * e = e * (f⁻¹ * ((c : G) * S.z * (c : G)⁻¹)) * K.t
    set w := f⁻¹ * ((c : G) * S.z * (c : G)⁻¹) with hw
    have hwt : w * K.t = K.t * w := by
      have h1 : (c : G) * S.z * (c : G)⁻¹ * K.t = K.t * ((c : G) * S.z * (c : G)⁻¹) :=
        (K.pair c hyM hyz).t_comm_x.symm
      have h2 : f⁻¹ * K.t = K.t * f⁻¹ := by
        calc f⁻¹ * K.t = f⁻¹ * (K.t * f) * f⁻¹ := by group
          _ = f⁻¹ * (f * K.t) * f⁻¹ := by rw [hft]
          _ = K.t * f⁻¹ := by group
      rw [hw, mul_assoc, h1, ← mul_assoc, h2, mul_assoc]
    have het : (e : G) * K.t = K.t * e := mem_centralizer_singleton_iff.mp e.2
    rcases h with h | h
    · left
      calc w * (e : G) = w * (e : G) * w⁻¹ * (e : G)⁻¹ * ((e : G) * w) := by group
        _ = (e : G) * w := by rw [h, one_mul]
    · right
      calc w * (e : G) = w * (e : G) * w⁻¹ * (e : G)⁻¹ * ((e : G) * w) := by group
        _ = K.t * ((e : G) * w) := by rw [h]
        _ = (K.t * (e : G)) * w := by group
        _ = (e : G) * (K.t * w) := by rw [← het]; group
        _ = (e : G) * w * K.t := by rw [← hwt]; group

theorem oddCore_gen (hn : 3 ≤ S.width)
    (hτ : ∃ τ ∈ Timmesfeld.CorB.conjCent K.zeta, τ ≠ K.zeta) :
    ∀ N : Subgroup (Cbar K.t), N.Normal → Odd (Nat.card N) → N = ⊥ := by
  intro N hN hodd
  have h2F : IsPGroup 2 K.Fbar := K.isPGroup_Hbar.to_le K.Fbar_le_Hbar
  have h1 : ∀ n ∈ N, n * K.zeta = K.zeta * n → n = 1 := by
    intro n hnN hnz
    have hnC : n ∈ centralizer ({K.zeta} : Set (Cbar K.t)) :=
      mem_centralizer_singleton_iff.mpr hnz
    have hnF : n ∈ centralizer (K.Fbar : Set (Cbar K.t)) := by
      rw [mem_centralizer_iff]
      intro x hx
      have hmN : n * x * n⁻¹ * x⁻¹ ∈ N := by
        have := N.mul_mem hnN (hN.conj_mem _ (N.inv_mem hnN) x)
        rwa [show n * (x * n⁻¹ * x⁻¹) = n * x * n⁻¹ * x⁻¹ by group] at this
      have hmF : n * x * n⁻¹ * x⁻¹ ∈ K.Fbar :=
        K.Fbar.mul_mem (K.conj_mem_Fbar hnC hx) (K.Fbar.inv_mem hx)
      have hc := eq_one_of_mem_of_odd hodd h2F hmN hmF
      calc x * n = n * x * n⁻¹ * x⁻¹ * (x * n) := by rw [hc, one_mul]
        _ = n * x := by group
    exact eq_one_of_mem_of_odd hodd K.isPGroup_Hbar hnN (K.centralizer_Fbar_le_Hbar hnF)
  have h2 : ∀ y, IsConj K.zeta y → ∀ n ∈ N, n * y = y * n → n = 1 := by
    intro y hy n hnN hny
    obtain ⟨k, rfl⟩ := isConj_iff.mp hy
    have h3 := h1 (k⁻¹ * n * k) (by simpa using hN.conj_mem n hnN k⁻¹) (by
      calc k⁻¹ * n * k * K.zeta = k⁻¹ * (n * (k * K.zeta * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * K.zeta * k⁻¹) * n) * k := by rw [hny]
        _ = K.zeta * (k⁻¹ * n * k) := by group)
    calc n = k * (k⁻¹ * n * k) * k⁻¹ := by group
      _ = 1 := by rw [h3]; group
  obtain ⟨τ, hτc, hτne⟩ := hτ
  obtain ⟨f, -, -, hf⟩ := K.exists_fusion_gen hn hτc hτne
  have hζτ : IsConj K.zeta (K.zeta * τ) := hτc.2.trans (isConj_iff.mpr ⟨f, hf⟩)
  have hτ2 : τ * τ = 1 := by
    obtain ⟨k, hk⟩ := isConj_iff.mp hτc.2
    rw [← hk]
    calc k * K.zeta * k⁻¹ * (k * K.zeta * k⁻¹) = k * (K.zeta * K.zeta) * k⁻¹ := by group
      _ = 1 := by rw [K.zeta_mul_zeta]; group
  have hinv : ∀ y, IsConj K.zeta y → y * y = 1 → ∀ n ∈ N, y * n * y⁻¹ = n⁻¹ := by
    intro y hy hyy n hn
    exact conj_eq_inv_of_fixedPointFree (fun k hk => hN.conj_mem k hk y) hyy
      (fun k hk hky => h2 y hy k hk hky) hn
  rw [eq_bot_iff]
  intro n hn
  rw [mem_bot]
  refine h2 _ hζτ n hn ?_
  have hz1 := hinv K.zeta (IsConj.refl _) K.zeta_mul_zeta
  have hτ1 := hinv τ hτc.2 hτ2
  have e1 : K.zeta * τ * n * (K.zeta * τ)⁻¹ = n := by
    calc K.zeta * τ * n * (K.zeta * τ)⁻¹ = K.zeta * (τ * n * τ⁻¹) * K.zeta⁻¹ := by group
      _ = K.zeta * n⁻¹ * K.zeta⁻¹ := by rw [hτ1 n hn]
      _ = (K.zeta * n * K.zeta⁻¹)⁻¹ := by group
      _ = n := by rw [hz1 n hn, inv_inv]
  calc n * (K.zeta * τ) = (K.zeta * τ * n * (K.zeta * τ)⁻¹) * (K.zeta * τ) := by rw [e1]
    _ = (K.zeta * τ) * n := by group

theorem smithHyp_gen (hn : 3 ≤ S.width)
    (hτ : ∃ τ ∈ Timmesfeld.CorB.conjCent K.zeta, τ ≠ K.zeta) : SmithHyp K.zeta K.Fbar where
  orderOf_eq := K.orderOf_zeta
  oddCore := K.oddCore_gen hn hτ
  le_centralizer := K.Fbar_le_centralizer
  conj_mem := fun _ hc _ hf => K.conj_mem_Fbar hc hf
  extraspecial := K.isExtraspecial_Fbar hn
  zeta_mem := K.zeta_mem_Fbar
  width := K.card_Fbar hn
  elemAb := fun _ ha _ hb =>
    K.mem_zpowers_of_mem_Hbar (K.sup_centralizer_le_Hbar ha) (K.sup_centralizer_le_Hbar hb)
  conj_mem_E := fun _ hτ hτc => K.conj_mem_E_gen hn hτ hτc
  conj_mem_F := fun _ hτF hτ => K.eq_zeta_of_mem_Fbar hτF hτ

end Six

end S63

end CFSG.LargeExtraspecial

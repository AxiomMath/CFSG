module

public import CFSG.LocalAnalysis.EvenBN.GMS.LocalFusion

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

section General

variable {H : Type*} [Group H]

theorem inf_centralizer_mul_eq {K : Subgroup H} {e p : H} (he : ∀ k ∈ K, e * k = k * e) :
    K ⊓ centralizer ({e * p} : Set H) = K ⊓ centralizer ({p} : Set H) := by
  ext k
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine ⟨fun ⟨hk, hc⟩ => ⟨hk, ?_⟩, fun ⟨hk, hc⟩ => ⟨hk, ?_⟩⟩
  · have h1 : e * (k * p) = e * (p * k) := by
      calc e * (k * p) = (e * k) * p := by group
        _ = (k * e) * p := by rw [he k hk]
        _ = k * (e * p) := by group
        _ = e * p * k := hc
        _ = e * (p * k) := by group
    exact mul_left_cancel h1
  · calc k * (e * p) = (k * e) * p := by group
      _ = (e * k) * p := by rw [he k hk]
      _ = e * (k * p) := by group
      _ = e * (p * k) := by rw [hc]
      _ = e * p * k := by group

end General

namespace LocalSetting

variable {H : Type*} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}

section Affine

variable (h : LocalSetting A t U V D n)
include h

theorem t_mem_normalizer_U : t ∈ normalizer (U : Set H) :=
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun u hu => h.t_mul_comm u hu)

theorem conj_mul_eq : ∀ v ∈ V, ∀ u ∈ U, v * (t * u) * v⁻¹ = t * ((v * t * v⁻¹ * t) * u) := by
  intro v hv u hu
  have hvu : v * u = u * v := h.V_comm v hv u (h.U_le_V hu)
  have hc := h.comm_mem v hv
  have e1 : v * u * v⁻¹ = u := by rw [hvu, mul_inv_cancel_right]
  have e2 : v * t * v⁻¹ * t * t = v * t * v⁻¹ := by
    rw [mul_assoc (v * t * v⁻¹) t t, h.t_mul_t, mul_one]
  calc v * (t * u) * v⁻¹ = (v * t * v⁻¹) * (v * u * v⁻¹) := by group
    _ = v * t * v⁻¹ * t * t * u := by rw [e1, e2]
    _ = t * ((v * t * v⁻¹ * t) * u) := by rw [h.t_mul_comm _ hc]; group

theorem V_le_normalizer_B : V ≤ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H) := by
  refine le_normalizer_of_conj_mem fun v hv b hb => ?_
  rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t h.t_mem_normalizer_U hb with
    hbU | ⟨u, hu, rfl⟩
  · have e1 : v * b * v⁻¹ = b := by
      rw [h.V_comm v hv b (h.U_le_V hbU), mul_inv_cancel_right]
    rw [e1]
    exact mem_sup_left hbU
  · rw [h.t_mul_comm u hu, h.conj_mul_eq v hv u hu]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (mul_mem (h.comm_mem v hv) hu))

theorem exists_inv_mul_mem_centralizer {x : H}
    (hx : x ∈ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H)) :
    ∃ v ∈ V, v⁻¹ * x ∈ centralizer ({t} : Set H) := by
  obtain ⟨c, hc, hxc⟩ := h.exists_conj_t_eq hx
  obtain ⟨w, hw, hwc⟩ := h.exists_conj_V c hc
  refine ⟨w⁻¹, inv_mem hw, mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 : x * t * x⁻¹ = w⁻¹ * t * w := by rw [hxc, hwc]
  calc w⁻¹⁻¹ * x * t = w * (x * t * x⁻¹) * x := by group
    _ = w * (w⁻¹ * t * w) * x := by rw [h1]
    _ = t * (w⁻¹⁻¹ * x) := by group

end Affine

section Characteristic

variable (h : LocalSetting A t U V D n)
include h

theorem V_inf_T {T : Subgroup H} (hTt : T ≤ centralizer ({t} : Set H)) (hUT : U ≤ T) :
    V ⊓ T = U := by
  refine le_antisymm ?_ (le_inf h.U_le_V hUT)
  rw [← h.V_inf_centralizer]
  exact inf_le_inf_left V hTt

theorem mul_t_mul_self_iff : ∀ v ∈ V, v * t * (v * t) = 1 ↔ v ∈ U := by
  intro v hv
  rw [← h.comm_eq_one_iff v hv]
  have hv1 : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.V_mul_self v hv)
  rw [hv1]
  simp only [mul_assoc]

theorem exists_eq_mul_of_conj_mem_Vt (g : H) (hg : g⁻¹ * t * g ∈ V ⊔ zpowers t) :
    ∃ u ∈ U, g⁻¹ * t * g = t * u := by
  rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t h.t_mem_normalizer_V hg with
    hV | ⟨v, hv, hvt⟩
  · exact absurd hV (h.conj_not_mem_V g)
  have hinv : v * t * (v * t) = 1 := by
    rw [← hvt]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [h.t_mul_t]; group
  have hvU := (h.mul_t_mul_self_iff v hv).mp hinv
  exact ⟨v, hvU, by rw [hvt, h.t_mul_comm v hvU]⟩

theorem normalizer_Vt_le_normalizer_V :
    normalizer ((V ⊔ zpowers t : Subgroup H) : Set H) ≤ normalizer (V : Set H) := by
  refine le_normalizer_of_conj_mem fun x hx w hw => ?_
  have h1 := (mem_normalizer_iff.mp hx w).mp (mem_sup_left hw)
  rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t h.t_mem_normalizer_V h1 with
    hV | ⟨v, hv, hvt⟩
  · exact hV
  exfalso
  have hinv : v * t * (v * t) = 1 := by
    rw [← hvt]
    calc x * w * x⁻¹ * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
      _ = 1 := by rw [h.V_mul_self w hw]; group
  have hvU := (h.mul_t_mul_self_iff v hv).mp hinv
  obtain ⟨v', -, hv'⟩ := h.exists_conj_V v hvU
  apply h.conj_not_mem_V (v' * x)
  have h2 : (v' * x)⁻¹ * t * (v' * x) = w := by
    calc (v' * x)⁻¹ * t * (v' * x) = x⁻¹ * (v'⁻¹ * t * v') * x := by group
      _ = x⁻¹ * (v * t) * x := by rw [hv', h.t_mul_comm v hvU]
      _ = x⁻¹ * (x * w * x⁻¹) * x := by rw [hvt]
      _ = w := by group
  rw [h2]
  exact hw

theorem normalizer_Vt_le_normalizer_B :
    normalizer ((V ⊔ zpowers t : Subgroup H) : Set H) ≤
      normalizer ((U ⊔ zpowers t : Subgroup H) : Set H) := by
  have htU : ∀ x ∈ normalizer ((V ⊔ zpowers t : Subgroup H) : Set H), ∀ u ∈ U,
      ∃ c ∈ U, x * (t * u) * x⁻¹ = t * c := by
    intro x hx u hu
    obtain ⟨w, hw, hwu⟩ := h.exists_conj_V u hu
    have hmem : (w * x⁻¹)⁻¹ * t * (w * x⁻¹) ∈ V ⊔ zpowers t := by
      have e1 : (w * x⁻¹)⁻¹ * t * (w * x⁻¹) = x * (t * u) * x⁻¹ := by
        rw [← hwu]
        group
      rw [e1]
      exact (mem_normalizer_iff.mp hx _).mp
        (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (h.U_le_V hu)))
    obtain ⟨c, hc, hce⟩ := h.exists_eq_mul_of_conj_mem_Vt _ hmem
    refine ⟨c, hc, ?_⟩
    rw [← hce, ← hwu]
    group
  refine le_normalizer_of_conj_mem fun x hx b hb => ?_
  obtain ⟨c₀, hc₀, hx0⟩ := htU x hx 1 (one_mem U)
  rw [mul_one] at hx0
  rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t h.t_mem_normalizer_U hb with
    hbU | ⟨u, hu, rfl⟩
  · obtain ⟨c, hc, hxc⟩ := htU x hx b hbU
    have e1 : x * b * x⁻¹ = (x * t * x⁻¹)⁻¹ * (x * (t * b) * x⁻¹) := by group
    have e2 : (t * c₀)⁻¹ * (t * c) = c₀⁻¹ * c := by group
    rw [e1, hx0, hxc, e2]
    exact mem_sup_left (mul_mem (inv_mem hc₀) hc)
  · obtain ⟨c, hc, hxc⟩ := htU x hx u hu
    rw [h.t_mul_comm u hu, hxc]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hc)

end Characteristic

section Sylow

variable (h : LocalSetting A t U V D n)
include h

theorem mem_centralizer_B_iff {x : H} :
    x ∈ centralizer ((U ⊔ zpowers t : Subgroup H) : Set H) ↔
      x ∈ centralizer ({t} : Set H) ∧ x ∈ centralizer (U : Set H) := by
  constructor
  · intro hx
    refine ⟨mem_centralizer_singleton_iff.mpr ?_,
      centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hx⟩
    exact (mem_centralizer_iff.mp hx t (mem_sup_right (mem_zpowers t))).symm
  · rintro ⟨hxt, hxU⟩
    refine mem_centralizer_iff.mpr fun b hb => ?_
    have hxt' : x * t = t * x := mem_centralizer_singleton_iff.mp hxt
    rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t h.t_mem_normalizer_U hb with
      hbU | ⟨u, hu, rfl⟩
    · exact mem_centralizer_iff.mp hxU b hbU
    · have hux : u * x = x * u := mem_centralizer_iff.mp hxU u hu
      calc u * t * x = u * (x * t) := by rw [mul_assoc, ← hxt']
        _ = x * (u * t) := by rw [← mul_assoc, hux, mul_assoc]

theorem t_mem_centralizer_B : t ∈ centralizer ((U ⊔ zpowers t : Subgroup H) : Set H) :=
  h.mem_centralizer_B_iff.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
    mem_centralizer_iff.mpr fun u hu => h.t_mul_comm u hu⟩

theorem isPGroup_B : IsPGroup 2 (U ⊔ zpowers t : Subgroup H) := by
  obtain ⟨T, hT, hUT⟩ := h.exists_isSylowOf
  exact hT.isPGroup.to_le (h.B_le_T hT hUT)

theorem le_B_of_le_centralizer {X : Subgroup H}
    (hXC : X ≤ centralizer ((U ⊔ zpowers t : Subgroup H) : Set H)) (hX : IsPGroup 2 X) :
    X ≤ U ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN : X ≤ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H) :=
    hXC.trans (Subgroup.centralizer_le_normalizer _)
  have hXB := IsPGroup.to_sup_of_normal_right' hX h.isPGroup_B hXN
  have hXBt : X ⊔ (U ⊔ zpowers t) ≤ centralizer ({t} : Set H) :=
    sup_le (fun x hx => (h.mem_centralizer_B_iff.mp (hXC hx)).1)
      (sup_le h.U_le_centralizer (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)))
  obtain ⟨T, hT, hXT⟩ := exists_isSylowOf_le hXBt hXB
  have hUT : U ≤ T := le_sup_left.trans (le_sup_right.trans hXT)
  intro x hx
  rw [← h.T_inf_centralizer_U hT hUT]
  exact mem_inf.mpr ⟨hXT (mem_sup_left hx), (h.mem_centralizer_B_iff.mp (hXC hx)).2⟩

theorem normalizer_B_le_normalizer_sup :
    normalizer ((U ⊔ zpowers t : Subgroup H) : Set H) ≤
      normalizer ((V ⊔ centralizer ((U ⊔ zpowers t : Subgroup H) : Set H) : Subgroup H) :
        Set H) := by
  set B := U ⊔ zpowers t with hBdef
  set C := centralizer (B : Set H) with hCdef
  refine le_normalizer_of_conj_mem fun x hx k hk => ?_
  have hmap : (V ⊔ C).map (MulAut.conj x).toMonoidHom ≤ V ⊔ C := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      change x * v * x⁻¹ ∈ V ⊔ C
      have hg : x * v * x⁻¹ ∈ normalizer (B : Set H) :=
        mul_mem (mul_mem hx (h.V_le_normalizer_B hv)) (inv_mem hx)
      obtain ⟨v', hv', hk'⟩ := h.exists_inv_mul_mem_centralizer hg
      have hgu : ∀ u ∈ U, x * v * x⁻¹ * u = u * (x * v * x⁻¹) := by
        intro u hu
        have hxu : x⁻¹ * u * x ∈ U := by
          have h1 := (mem_normalizer_iff.mp (h.normalizer_B_le (inv_mem hx)) u).mp hu
          rwa [inv_inv] at h1
        have hvu : v * (x⁻¹ * u * x) = (x⁻¹ * u * x) * v := h.V_comm v hv _ (h.U_le_V hxu)
        calc x * v * x⁻¹ * u = x * (v * (x⁻¹ * u * x)) * x⁻¹ := by group
          _ = x * ((x⁻¹ * u * x) * v) * x⁻¹ := by rw [hvu]
          _ = u * (x * v * x⁻¹) := by group
      have hkU : v'⁻¹ * (x * v * x⁻¹) ∈ centralizer (U : Set H) := by
        refine mem_centralizer_iff.mpr fun u hu => ?_
        have hv'u : v'⁻¹ * u = u * v'⁻¹ := by
          have h1 : v' * u = u * v' := h.V_comm v' hv' u (h.U_le_V hu)
          calc v'⁻¹ * u = v'⁻¹ * (u * v') * v'⁻¹ := by group
            _ = v'⁻¹ * (v' * u) * v'⁻¹ := by rw [h1]
            _ = u * v'⁻¹ := by group
        calc u * (v'⁻¹ * (x * v * x⁻¹)) = (u * v'⁻¹) * (x * v * x⁻¹) := by group
          _ = (v'⁻¹ * u) * (x * v * x⁻¹) := by rw [hv'u]
          _ = v'⁻¹ * (u * (x * v * x⁻¹)) := by group
          _ = v'⁻¹ * (x * v * x⁻¹ * u) := by rw [hgu u hu]
          _ = v'⁻¹ * (x * v * x⁻¹) * u := by group
      have hkC : v'⁻¹ * (x * v * x⁻¹) ∈ C := h.mem_centralizer_B_iff.mpr ⟨hk', hkU⟩
      have e1 : x * v * x⁻¹ = v' * (v'⁻¹ * (x * v * x⁻¹)) := by group
      rw [e1]
      exact mul_mem (mem_sup_left hv') (mem_sup_right hkC)
    · rintro _ ⟨c, hc, rfl⟩
      change x * c * x⁻¹ ∈ V ⊔ C
      refine mem_sup_right (mem_centralizer_iff.mpr fun b hb => ?_)
      have hb' : x⁻¹ * b * x ∈ B := by
        have h1 := (mem_normalizer_iff.mp (inv_mem hx) b).mp hb
        rwa [inv_inv] at h1
      have h1 := mem_centralizer_iff.mp hc _ hb'
      calc b * (x * c * x⁻¹) = x * ((x⁻¹ * b * x) * c) * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * b * x)) * x⁻¹ := by rw [h1]
        _ = x * c * x⁻¹ * b := by group
  exact hmap ⟨k, hk, rfl⟩

theorem inf_sup_centralizer_eq {S : Subgroup H}
    (hSN : S ≤ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H)) (hS : IsPGroup 2 S)
    (hVS : V ⊔ zpowers t ≤ S) :
    S ⊓ (V ⊔ centralizer ((U ⊔ zpowers t : Subgroup H) : Set H)) = V ⊔ zpowers t := by
  refine le_antisymm (fun s hs => ?_)
    (le_inf hVS (sup_le le_sup_left (zpowers_le.mpr (mem_sup_right h.t_mem_centralizer_B))))
  obtain ⟨hsS, hsVC⟩ := mem_inf.mp hs
  obtain ⟨v, hv, hvs⟩ := h.exists_inv_mul_mem_centralizer (hSN hsS)
  have hvS : v ∈ S := hVS (mem_sup_left hv)
  have hkS : v⁻¹ * s ∈ S := mul_mem (inv_mem hvS) hsS
  have hVCU : V ⊔ centralizer ((U ⊔ zpowers t : Subgroup H) : Set H) ≤
      centralizer (U : Set H) :=
    sup_le (fun w hw => mem_centralizer_iff.mpr fun u hu => h.V_comm u (h.U_le_V hu) w hw)
      (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  have hkU : v⁻¹ * s ∈ centralizer (U : Set H) :=
    hVCU (mul_mem (inv_mem (mem_sup_left hv)) hsVC)
  have hkC : v⁻¹ * s ∈ centralizer ((U ⊔ zpowers t : Subgroup H) : Set H) :=
    h.mem_centralizer_B_iff.mpr ⟨hvs, hkU⟩
  have hkB : v⁻¹ * s ∈ U ⊔ zpowers t :=
    h.le_B_of_le_centralizer (inf_le_right :
      S ⊓ centralizer ((U ⊔ zpowers t : Subgroup H) : Set H) ≤ _) (hS.to_le inf_le_left)
      (mem_inf.mpr ⟨hkS, hkC⟩)
  have e1 : s = v * (v⁻¹ * s) := by group
  rw [e1]
  exact mul_mem (mem_sup_left hv)
    ((sup_le (h.U_le_V.trans le_sup_left) le_sup_right : U ⊔ zpowers t ≤ V ⊔ zpowers t) hkB)

theorem le_normalizer_Vt {S : Subgroup H}
    (hSN : S ≤ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H)) (hS : IsPGroup 2 S)
    (hVS : V ⊔ zpowers t ≤ S) : S ≤ normalizer ((V ⊔ zpowers t : Subgroup H) : Set H) := by
  rw [← h.inf_sup_centralizer_eq hSN hS hVS]
  exact (le_inf le_normalizer (hSN.trans h.normalizer_B_le_normalizer_sup)).trans
    inf_normalizer_le_normalizer_inf

theorem isPGroup_Vt : IsPGroup 2 (V ⊔ zpowers t : Subgroup H) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.to_sup_of_normal_left' (@IsElementaryAbelian.isPGroup 2 V _ h.isElementaryAbelian_V)
    h.isPGroup_zpowers (zpowers_le.mpr h.t_mem_normalizer_V)

theorem Vt_le_normalizer_B :
    V ⊔ zpowers t ≤ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H) :=
  sup_le h.V_le_normalizer_B (zpowers_le.mpr (le_normalizer (mem_sup_right (mem_zpowers t))))

theorem exists_isSylowOf_le_normalizer : ∃ T : Subgroup H,
    IsSylowOf 2 T (centralizer ({t} : Set H)) ∧ U ≤ T ∧
      T ≤ normalizer ((V ⊔ zpowers t : Subgroup H) : Set H) ∧ T ≤ normalizer (V : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hVS⟩ := exists_isSylowOf_le h.Vt_le_normalizer_B h.isPGroup_Vt
  have hSV := h.le_normalizer_Vt hS.le hS.isPGroup hVS
  set T₁ := S ⊓ centralizer ({t} : Set H) with hT₁def
  have hUT₁ : U ≤ T₁ := le_inf (h.U_le_V.trans (le_sup_left.trans hVS)) h.U_le_centralizer
  have hT₁2 : IsPGroup 2 T₁ := hS.isPGroup.to_le inf_le_left
  obtain ⟨T', hT', hT₁T'⟩ := exists_isSylowOf_le (inf_le_right : T₁ ≤ _) hT₁2
  have hUT' : U ≤ T' := hUT₁.trans hT₁T'
  obtain ⟨S', hS', hT'S'⟩ := exists_isSylowOf_le (h.T_le_normalizer_B hT' hUT') hT'.isPGroup
  obtain ⟨y, hy, hyS⟩ := hS.exists_mem_conj hS'
  obtain ⟨v, hv, hvy⟩ := h.exists_inv_mul_mem_centralizer (inv_mem hy)
  have hz : y * v ∈ centralizer ({t} : Set H) := by
    have e1 : y * v = (v⁻¹ * y⁻¹)⁻¹ := by group
    rw [e1]
    exact inv_mem hvy
  have hvS : v ∈ S := hVS (mem_sup_left hv)
  have hle : T'.map (MulAut.conj (y * v)⁻¹).toMonoidHom ≤ T₁ := by
    rintro _ ⟨s, hs, rfl⟩
    change (MulAut.conj (y * v)⁻¹) s ∈ T₁
    rw [MulAut.conj_apply, inv_inv]
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem (inv_mem hz) (hT'.le hs)) hz⟩
    have h1 := (hyS s).mp (hT'S' hs)
    have e2 : (y * v)⁻¹ * s * (y * v) = v⁻¹ * (y⁻¹ * s * y) * v := by group
    rw [e2]
    exact mul_mem (mul_mem (inv_mem hvS) h1) hvS
  have hcard : Nat.card T' ≤ Nat.card T₁ := by
    have h2 := card_le_of_le hle
    rwa [card_map_of_injective (MulAut.conj (y * v)⁻¹).injective] at h2
  have heq : T₁ = T' := eq_of_le_of_card_ge hT₁T' hcard
  refine ⟨T₁, heq ▸ hT', hUT₁, inf_le_left.trans hSV,
    (inf_le_left.trans hSV).trans h.normalizer_Vt_le_normalizer_V⟩

theorem isSylowOf_sup {T : Subgroup H} (hT : IsSylowOf 2 T (centralizer ({t} : Set H)))
    (hUT : U ≤ T) (hTV : T ≤ normalizer (V : Set H)) :
    IsSylowOf 2 (V ⊔ T) (normalizer ((U ⊔ zpowers t : Subgroup H) : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVT2 : IsPGroup 2 (V ⊔ T : Subgroup H) :=
    IsPGroup.to_sup_of_normal_left' (@IsElementaryAbelian.isPGroup 2 V _ h.isElementaryAbelian_V)
      hT.isPGroup hTV
  have hVTN : V ⊔ T ≤ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H) :=
    sup_le h.V_le_normalizer_B (h.T_le_normalizer_B hT hUT)
  obtain ⟨S, hS, hVTS⟩ := exists_isSylowOf_le hVTN hVT2
  have hST : S ⊓ centralizer ({t} : Set H) = T :=
    hT.eq_of_le (le_inf (le_sup_right.trans hVTS) hT.le) inf_le_right
      (hS.isPGroup.to_le inf_le_left)
  have hSle : S ≤ V ⊔ T := by
    intro s hs
    obtain ⟨v, hv, hvs⟩ := h.exists_inv_mul_mem_centralizer (hS.le hs)
    have hk : v⁻¹ * s ∈ T := by
      rw [← hST]
      exact mem_inf.mpr ⟨mul_mem (inv_mem (hVTS (mem_sup_left hv))) hs, hvs⟩
    have e1 : s = v * (v⁻¹ * s) := by group
    rw [e1]
    exact mul_mem (mem_sup_left hv) (mem_sup_right hk)
  rwa [le_antisymm hSle hVTS] at hS

end Sylow

section Bound

variable (h : LocalSetting A t U V D n)
include h

theorem comm_conj {T : Subgroup H} (hTt : T ≤ centralizer ({t} : Set H))
    (hTV : T ≤ normalizer (V : Set H)) {y : H} (hy : y ∈ V ⊔ T) {w : H} (hw : w ∈ V) :
    (y * w * y⁻¹) * t * (y * w * y⁻¹)⁻¹ * t = y * (w * t * w⁻¹ * t) * y⁻¹ := by
  have hy' : y ∈ ((V ⊔ T : Subgroup H) : Set H) := hy
  rw [coe_mul_of_right_le_normalizer_left V T hTV] at hy'
  obtain ⟨v, hv, p, hp, hvp⟩ := hy'
  have hvp' : y = v * p := hvp.symm
  subst hvp'
  have hyN : v * p ∈ normalizer (V : Set H) := mul_mem (le_normalizer hv) (hTV hp)
  have hw' : v * p * w * (v * p)⁻¹ ∈ V := (mem_normalizer_iff.mp hyN w).mp hw
  set w' := v * p * w * (v * p)⁻¹ with hw'def
  have hpt : p * t = t * p := mem_centralizer_singleton_iff.mp (hTt hp)
  have hyt : v * p * t * (v * p)⁻¹ = v * t * v⁻¹ := by
    calc v * p * t * (v * p)⁻¹ = v * (p * t) * p⁻¹ * v⁻¹ := by group
      _ = v * (t * p) * p⁻¹ * v⁻¹ := by rw [hpt]
      _ = v * t * v⁻¹ := by group
  have hc : w' * t * w'⁻¹ * t ∈ U := h.comm_mem w' hw'
  have hvw : v * w' = w' * v := h.V_comm v hv w' hw'
  have hvc : v * (w' * t * w'⁻¹ * t) = (w' * t * w'⁻¹ * t) * v :=
    h.V_comm v hv _ (h.U_le_V hc)
  have hvw' : w'⁻¹ * v⁻¹ = v⁻¹ * w'⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hvw]
  have hR : v * p * (w * t * w⁻¹ * t) * (v * p)⁻¹ =
      w' * (v * p * t * (v * p)⁻¹) * w'⁻¹ * (v * p * t * (v * p)⁻¹) := by
    rw [hw'def]
    group
  rw [hR, hyt]
  calc w' * t * w'⁻¹ * t = v * (w' * t * w'⁻¹ * t) * v⁻¹ := by rw [hvc, mul_inv_cancel_right]
    _ = (v * w') * t * (w'⁻¹ * v⁻¹ * v) * t * v⁻¹ := by group
    _ = (w' * v) * t * (v⁻¹ * w'⁻¹ * v) * t * v⁻¹ := by rw [hvw, hvw']
    _ = w' * (v * t * v⁻¹) * w'⁻¹ * (v * t * v⁻¹) := by group

theorem card_inf_centralizer_le_sq {T : Subgroup H} (hTt : T ≤ centralizer ({t} : Set H))
    (hTV : T ≤ normalizer (V : Set H)) {y : H} (hy : y ∈ V ⊔ T) :
    Nat.card (V ⊓ centralizer ({y} : Set H) : Subgroup H) ≤
      Nat.card (U ⊓ centralizer ({y} : Set H) : Subgroup H) ^ 2 := by
  classical
  set K := V ⊓ centralizer ({y} : Set H) with hKdef
  set M := U ⊓ centralizer ({y} : Set H) with hMdef
  have hyc : ∀ w ∈ K, y * w * y⁻¹ = w := fun w hw => by
    rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp hw).2, mul_inv_cancel_right]
  have hmem : ∀ w ∈ K, w * t * w⁻¹ * t ∈ M := fun w hw => by
    refine mem_inf.mpr ⟨h.comm_mem w (mem_inf.mp hw).1, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := h.comm_conj hTt hTV hy (mem_inf.mp hw).1
    rw [hyc w hw] at h1
    calc w * t * w⁻¹ * t * y = y * (w * t * w⁻¹ * t) * y⁻¹ * y := by rw [← h1]
      _ = y * (w * t * w⁻¹ * t) := by group
  let φ : K →* M :=
    { toFun := fun w => ⟨w * t * (w : H)⁻¹ * t, hmem w w.2⟩
      map_one' := Subtype.ext (by simp [h.t_mul_t])
      map_mul' := fun a b => Subtype.ext (h.comm_mul a (mem_inf.mp a.2).1 b (mem_inf.mp b.2).1) }
  have hker : ∀ w : K, w ∈ φ.ker → (w : H) ∈ M := fun w hw => by
    refine mem_inf.mpr ⟨(h.comm_eq_one_iff w (mem_inf.mp w.2).1).mp ?_, (mem_inf.mp w.2).2⟩
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hw)
  have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have h2 : Nat.card φ.ker ≤ Nat.card M :=
    Nat.card_le_card_of_injective (fun w => ⟨w.1.1, hker w.1 w.2⟩) (fun a b hab => by
      have h' := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h'))
  have h3 : Nat.card φ.range ≤ Nat.card M := card_le_card_group _
  calc Nat.card K = Nat.card φ.range * Nat.card φ.ker := h1
    _ ≤ Nat.card M * Nat.card M := Nat.mul_le_mul h3 h2
    _ = Nat.card M ^ 2 := (sq _).symm

theorem card_inf_centralizer_le {T : Subgroup H} (hT : IsSylowOf 2 T (centralizer ({t} : Set H)))
    (hUT : U ≤ T) (hTV : T ≤ normalizer (V : Set H)) {y : H} (hy : y ∈ V ⊔ T) (hyV : y ∉ V) :
    Nat.card (V ⊓ centralizer ({y} : Set H) : Subgroup H) ≤ 2 ^ n := by
  have hy' : y ∈ ((V ⊔ T : Subgroup H) : Set H) := hy
  rw [coe_mul_of_right_le_normalizer_left V T hTV] at hy'
  obtain ⟨v, hv, p, hp, hvp⟩ := hy'
  have hvp' : y = v * p := hvp.symm
  by_cases hpB : p ∈ U ⊔ zpowers t
  · rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t h.t_mem_normalizer_U hpB with
      hpU | ⟨u, hu, hut⟩
    · exact absurd (hvp' ▸ mul_mem hv (h.U_le_V hpU)) hyV
    · have e1 : y = (v * u) * t := by rw [hvp', hut, mul_assoc]
      have e2 : V ⊓ centralizer ({y} : Set H) = V ⊓ centralizer ({t} : Set H) := by
        rw [e1]
        exact inf_centralizer_mul_eq fun k hk => h.V_comm _ (mul_mem hv (h.U_le_V hu)) k hk
      rw [e2, h.V_inf_centralizer, h.card_U]
  · have h1 := h.card_inf_centralizer_le_sq hT.le hTV hy
    have h2 : U ⊓ centralizer ({y} : Set H) = U ⊓ centralizer ({p} : Set H) := by
      rw [hvp']
      exact inf_centralizer_mul_eq fun k hk => h.V_comm v hv k (h.U_le_V hk)
    rw [h2] at h1
    exact h1.trans (h.card_inf_centralizer_sq_le hT hUT hp hpB)

end Bound

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.GMS

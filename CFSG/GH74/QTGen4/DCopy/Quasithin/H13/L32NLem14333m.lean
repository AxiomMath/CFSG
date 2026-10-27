module

public import CFSG.Quasithin.H13.L32NLem14333m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14333l

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits CFSG.Quasithin.SL3Model
open scoped commutatorElement MatrixGroups

namespace L14333

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Inv_F4

variable {T L V V₂ K : Subgroup G} {g a z b d x r : G} {D : HatModelU (fsuU T V)}
  (ι : Inv_F4 G T L V V₂ K g a z b d x r D)
include ι

theorem z_comm_F4 {t : G} (ht : t ∈ T) : t * z = z * t := by
  have h := ι.ctx.H_V1 t (ι.ctx.T_le ht).1 z ι.z_mem
  calc t * z = t * z * t⁻¹ * t := by group
    _ = z * t := by rw [h]

theorem card_cent_le_of_mem_F4 {y : G} (hyT : y ∈ T) (hy2 : y * y = 1)
    (hyP : y ∉ pCoreOf 2 L) (hyU : y ∉ fsuU T V) {p u : G} (hp : p ∈ pCoreOf 2 L)
    (hu : u ∈ fsuU T V) (hyeq : y = p * u) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) ≤ 2 ^ 7 ∧
      d ∈ T ⊓ Subgroup.centralizer ({y} : Set G) := by
  obtain ⟨hP, -⟩ := ι.pCoreOf_eq_F4 ι.hyp
  have hPab : ∀ u ∈ pCoreOf 2 L, ∀ w ∈ pCoreOf 2 L, u * w = w * u := hP ▸ ι.X_comm_F4
  have hyL : y ∈ L := by rw [hyeq]; exact L.mul_mem (pCoreOf_le 2 L hp) (ι.U_le_L_F4 ι.hyp hu)
  have hV1Z : fsuV1 T V ≤ centerOf (fsuU T V) := ι.vZ ▸ inf_le_right

  have hyZ : ∀ e ∈ centerOf (fsuU T V), y * e = e * y := by
    intro e he
    have heP : e ∈ pCoreOf 2 L := (le_sup_right.trans (ι.sup_zU_le_P_F4 ι.hyp)) he
    have h1 : p * e = e * p := hPab p hp e heP
    have h2 : u * e = e * u := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp he).2 u hu
    rw [hyeq]
    calc p * u * e = p * (u * e) := by group
      _ = p * (e * u) := by rw [h2]
      _ = (p * e) * u := by group
      _ = (e * p) * u := by rw [h1]
      _ = e * (p * u) := by group
  have hdC : d ∈ T ⊓ Subgroup.centralizer ({y} : Set G) :=
    ⟨ι.U_le_T_F4 ι.d_mem_U_F4, Subgroup.mem_centralizer_singleton_iff.mpr (hyZ d ι.d_mem).symm⟩
  refine ⟨?_, hdC⟩

  have hyK : y ∈ K := by rw [hyeq]; exact K.mul_mem (ι.P_le_K_F4 ι.hyp hp) (ι.U_le_K_F4 hu)
  have hyQ : y ∉ pCoreOf 2 (l32nH T V) := fun h => hyU (ι.mem_U_of_mem_L_F4 h hyL)
  have hfix := ι.ncard_fix_eq_four_F4 hyK hy2 hyQ
  set N := l32nH_le_normalizer_fsuU T V (le_of_mem_cComp ι.comp hyK)
  have hsub : (D.hat V : Set D.V) ⊆ {w : D.V | D.ρ ⟨y, N⟩ w = w} := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := ι.exists_of_mem_hatV_F4 hw
    have hvU := ι.ctx.V_U hv
    show D.ρ ⟨y, N⟩ (D.π v) = D.π v
    rw [D.ρ_π _ v hvU]
    show D.π (y * v * y⁻¹) = D.π v
    have hc : ⁅u, v⁆ ∈ fsuV1 T V := ι.ctx.comm u hu v hvU
    have huv : u * v * u⁻¹ ∈ V := ι.conj_mem_V_F4 (ι.U_le_L_F4 ι.hyp hu) hv
    have hpv : p * (u * v * u⁻¹) = (u * v * u⁻¹) * p :=
      (Subgroup.mem_centralizer_iff.mp (ι.P_le_centralizer_F4 hp) _ huv).symm
    have e1 : y * v * y⁻¹ = ⁅u, v⁆ * v := by
      rw [hyeq, commutatorElement_def]
      calc p * u * v * (p * u)⁻¹ = p * (u * v * u⁻¹) * p⁻¹ := by group
        _ = (u * v * u⁻¹) * p * p⁻¹ := by rw [hpv]
        _ = u * v * u⁻¹ * v⁻¹ * v := by group
    have hcU : ⁅u, v⁆ ∈ fsuU T V := (hV1Z hc).1
    rw [e1, D.π_mul _ hcU _ hvU, (L128A.HatU.π_eq_zero_iff D hcU).mpr (hV1Z hc), zero_add]
  have hhat : (D.hat V : Set D.V).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact ι.card_hatV
  have heq : (D.hat V : Set D.V) = {w : D.V | D.ρ ⟨y, N⟩ w = w} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hhat]; exact hfix.le) (Set.toFinite _)

  have hCU : fsuU T V ⊓ Subgroup.centralizer ({y} : Set G) ≤
      (V ⊓ Subgroup.centralizer ({y} : Set G)) ⊔ centerOf (fsuU T V) := by
    rintro s ⟨hsU, hsy⟩
    have hsy' : s * y = y * s := Subgroup.mem_centralizer_singleton_iff.mp hsy
    have hπ : D.π s ∈ (D.hat V : Set D.V) := by
      rw [heq]
      show D.ρ ⟨y, N⟩ (D.π s) = D.π s
      rw [D.ρ_π _ s hsU]
      show D.π (y * s * y⁻¹) = D.π s
      rw [← hsy', mul_inv_cancel_right]
    obtain ⟨v, hv, hvs⟩ := ι.exists_of_mem_hatV_F4 hπ
    have he : v⁻¹ * s ∈ centerOf (fsuU T V) := (D.π_eq_iff v (ι.ctx.V_U hv) s hsU).mp hvs
    set e := v⁻¹ * s with he'
    have h1 := hyZ e he
    have he1 : e⁻¹ * y = y * e⁻¹ := by
      calc e⁻¹ * y = e⁻¹ * (y * e) * e⁻¹ := by group
        _ = e⁻¹ * (e * y) * e⁻¹ := by rw [h1]
        _ = y * e⁻¹ := by group
    have hvy : v * y = y * v := by
      have hv' : v = s * e⁻¹ := by rw [he']; group
      rw [hv']
      calc s * e⁻¹ * y = s * (e⁻¹ * y) := by group
        _ = s * (y * e⁻¹) := by rw [he1]
        _ = (s * y) * e⁻¹ := by group
        _ = (y * s) * e⁻¹ := by rw [hsy']
        _ = y * (s * e⁻¹) := by group
    have hse : s = v * e := by rw [he']; group
    rw [hse]
    exact mul_mem (Subgroup.mem_sup_left ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr hvy⟩)
      (Subgroup.mem_sup_right he)

  have hcV := ι.card_cent_V_le_F4 hyL hyP
  have hZN : V ⊓ Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.normalizer (centerOf (fsuU T V) : Set G) :=
    fun v hv => l32nH_le_normalizer_zU (ι.ctx.U_le (ι.ctx.V_U hv.1))
  have h1 := L32NSet14.card_sup_mul_card_inf hZN
  rw [ι.card_zU] at h1
  have hV1le : fsuV1 T V ≤ (V ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ centerOf (fsuU T V) := by
    intro v hv
    have hvy : y * v * y⁻¹ = v := ι.ctx.H_V1 y (ι.ctx.T_le hyT).1 v hv
    refine ⟨⟨(Subgroup.mem_inf.mp hv).1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hV1Z hv⟩
    calc v * y = y * v * y⁻¹ * y := by rw [hvy]
      _ = y * v := by group
  have h2 := Subgroup.card_le_of_le hV1le
  rw [ι.ctx.card_V1] at h2
  have h3 : Nat.card ↥((V ⊓ Subgroup.centralizer ({y} : Set G)) ⊔ centerOf (fsuU T V)) * 2 ≤
      16 := by
    calc _ ≤ Nat.card ↥((V ⊓ Subgroup.centralizer ({y} : Set G)) ⊔ centerOf (fsuU T V)) *
          Nat.card ↥((V ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ centerOf (fsuU T V)) :=
          Nat.mul_le_mul_left _ h2
      _ = Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) * 4 := h1
      _ ≤ 4 * 4 := Nat.mul_le_mul_right _ hcV
  have hCU8 := (Subgroup.card_le_of_le hCU).trans (by omega : _ ≤ 8)

  set C := T ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hCN : C ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    fun t ht => l32nH_le_normalizer_fsuU T V (ι.ctx.T_le ht.1).1
  have h4 := L32NSet14.card_sup_mul_card_inf hCN
  rw [ι.card_U_F4] at h4
  have hT : Nat.card ↥T = 1024 := by rw [ι.card_T_eq_F4.1]; norm_num
  have h5 : Nat.card ↥(C ⊔ fsuU T V) ≤ 1024 :=
    (Subgroup.card_le_of_le (sup_le inf_le_left ι.U_le_T_F4)).trans hT.le
  have h6 : Nat.card ↥(C ⊓ fsuU T V) ≤ 8 :=
    (Subgroup.card_le_of_le (show C ⊓ fsuU T V ≤ fsuU T V ⊓ Subgroup.centralizer ({y} : Set G)
      from fun s hs => ⟨hs.2, hs.1.2⟩)).trans hCU8
  have h7 : Nat.card ↥C * 64 ≤ 1024 * 8 := by rw [← h4]; exact Nat.mul_le_mul h5 h6
  calc Nat.card ↥C ≤ 128 := by omega
    _ = 2 ^ 7 := by norm_num

theorem card_cent_le_of_not_mem_F4 {θ : ↥L →* SL(3, ZMod 2)}
    (hker : ∀ l : ↥L, θ l = 1 ↔ (l : G) ∈ pCoreOf 2 L)
    (hQv : ∀ q ∈ Qv (vE (ZMod 2) 0), ∃ u : ↥L, (u : G) ∈ fsuU T V ∧ θ u = q)
    {y : G} (hyT : y ∈ T) (hyL : y ∈ L) (hyP : y ∉ pCoreOf 2 L)
    (hR : θ ⟨y, hyL⟩ ∉ Qv (vE (ZMod 2) 0)) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) ≤ 2 ^ 7 ∧
      (2 ^ 7 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) →
        ∃ s ∈ T ⊓ Subgroup.centralizer ({y} : Set G), s * s = z) := by
  obtain ⟨hP, hPcard⟩ := ι.pCoreOf_eq_F4 ι.hyp
  have hPab : ∀ u ∈ pCoreOf 2 L, ∀ w ∈ pCoreOf 2 L, u * w = w * u := hP ▸ ι.X_comm_F4
  have hsqV : ∀ u ∈ pCoreOf 2 L, u * u ∈ V := hP ▸ ι.sq_mem_V_of_X_F4
  set C := T ⊓ Subgroup.centralizer ({y} : Set G) with hC
  set CP := pCoreOf 2 L ⊓ Subgroup.centralizer ({y} : Set G) with hCP
  set CV := V ⊓ Subgroup.centralizer ({y} : Set G) with hCV
  have hcV : Nat.card ↥CV ≤ 4 := ι.card_cent_V_le_F4 hyL hyP

  let f : ↥CP →* G :=
    { toFun := fun p => (p : G) * p
      map_one' := by simp
      map_mul' := fun p q => by
        show ((p : G) * q) * ((p : G) * q) = ((p : G) * p) * ((q : G) * q)
        have h := hPab _ q.2.1 _ p.2.1
        calc (p : G) * q * (p * q) = p * (q * p) * q := by group
          _ = p * (p * q) * q := by rw [h]
          _ = (p : G) * p * (q * q) := by group }
  have hfr : f.range ≤ CV := by
    rintro _ ⟨p, rfl⟩
    have hpy : (p : G) * y = y * p := Subgroup.mem_centralizer_singleton_iff.mp p.2.2
    refine ⟨hsqV _ p.2.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    show (p : G) * p * y = y * (p * p)
    calc (p : G) * p * y = p * (p * y) := by group
      _ = p * (y * p) := by rw [hpy]
      _ = (p * y) * p := by group
      _ = (y * p) * p := by rw [hpy]
      _ = y * (p * p) := by group
  have hfk : Nat.card ↥f.ker ≤ Nat.card ↥CV := by
    refine Nat.card_le_card_of_injective (fun k => (⟨((k : ↥CP) : G), ?_⟩ : ↥CV)) ?_
    · exact ⟨ι.mem_V_of_mul_self_F4 ι.hyp (k : ↥CP).2.1 (MonoidHom.mem_ker.mp k.2), (k : ↥CP).2.2⟩
    · intro k k' h
      have h' : ((k : ↥CP) : G) = ((k' : ↥CP) : G) := congrArg (fun w : ↥CV => (w : G)) h
      exact Subtype.ext (Subtype.ext h')
  have hfc := Subgroup.card_ker_mul_card_range f
  have hfrc := Subgroup.card_le_of_le hfr

  have hθT := card_eq_card_inf_mul_card_range θ hker (inf_le_right : T ⊓ L ≤ L)
  rw [ι.card_TL_F4 ι.hyp, show T ⊓ L ⊓ pCoreOf 2 L = pCoreOf 2 L from
    inf_eq_right.mpr (le_inf ι.P_le_T_F4 (pCoreOf_le 2 L)), hPcard] at hθT
  set BT := (θ.comp (Subgroup.inclusion (inf_le_right : T ⊓ L ≤ L))).range with hBT
  have hBT8 : Nat.card ↥BT = 8 := by norm_num at hθT; omega

  set W := BT ⊓ Subgroup.centralizer ({θ ⟨y, hyL⟩} : Set SL(3, ZMod 2)) with hW
  have hW4 : Nat.card ↥W ≤ 4 := by
    refine card_le_four_of_lt inf_le_left hBT8 fun hWB => ?_
    apply hR
    obtain ⟨b', c', hbc⟩ := sl3_centralizer_Qv (θ ⟨y, hyL⟩) fun b₀ c₀ => by
      obtain ⟨u, huU, hθu⟩ := hQv (tq b₀ c₀) (tq_mem_Qv b₀ c₀)
      have huT : (u : G) ∈ T ⊓ L := ⟨ι.U_le_T_F4 huU, u.2⟩
      have hmem : θ u ∈ W := by
        rw [hWB]
        exact ⟨⟨(u : G), huT⟩, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.mp hmem.2
      rw [← hθu]
      exact h.symm
    rw [hbc]
    exact tq_mem_Qv b' c'

  have hY := card_eq_card_inf_mul_card_range θ hker (inf_le_right : C ⊓ L ≤ L)
  have hYP : C ⊓ L ⊓ pCoreOf 2 L = CP := by
    ext q
    constructor
    · rintro ⟨⟨⟨-, hq⟩, -⟩, hqP⟩
      exact ⟨hqP, hq⟩
    · rintro ⟨hqP, hq⟩
      exact ⟨⟨⟨ι.P_le_T_F4 hqP, hq⟩, pCoreOf_le 2 L hqP⟩, hqP⟩
  rw [hYP] at hY
  have hYW : (θ.comp (Subgroup.inclusion (inf_le_right : C ⊓ L ≤ L))).range ≤ W := by
    rintro _ ⟨t, rfl⟩
    refine ⟨⟨⟨(t : G), t.2.1.1, t.2.2⟩, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hty : (t : G) * y = y * t := Subgroup.mem_centralizer_singleton_iff.mp t.2.1.2
    have e : (⟨(t : G), t.2.2⟩ : ↥L) * ⟨y, hyL⟩ = ⟨y, hyL⟩ * ⟨(t : G), t.2.2⟩ := Subtype.ext hty
    show θ ⟨(t : G), t.2.2⟩ * θ ⟨y, hyL⟩ = θ ⟨y, hyL⟩ * θ ⟨(t : G), t.2.2⟩
    rw [← map_mul, ← map_mul, e]
  have hYc := (Subgroup.card_le_of_le hYW).trans hW4

  have hrel : L.relIndex C ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := L) (inf_le_left : C ≤ T)
      (by rw [ι.card_T_eq_F4.2]; norm_num)
    rwa [ι.card_T_eq_F4.2] at h
  have hC2 := Subgroup.relIndex_mul_card L C
  rw [inf_comm] at hC2
  have hCle : Nat.card ↥C ≤ 2 * (Nat.card ↥CP * 4) := by
    calc Nat.card ↥C = L.relIndex C * Nat.card ↥(C ⊓ L) := hC2.symm
      _ ≤ 2 * Nat.card ↥(C ⊓ L) := Nat.mul_le_mul_right _ hrel
      _ ≤ 2 * (Nat.card ↥CP * 4) := by
          rw [hY]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hYc)
  have hCP16 : Nat.card ↥CP ≤ 16 := by
    rw [← hfc]
    calc Nat.card ↥f.ker * Nat.card ↥f.range ≤ 4 * 4 := Nat.mul_le_mul (hfk.trans hcV)
          (hfrc.trans hcV)
      _ = 16 := by norm_num
  refine ⟨?_, fun h128 => ?_⟩
  · calc Nat.card ↥C ≤ 2 * (16 * 4) := hCle.trans (by omega)
      _ = 2 ^ 7 := by norm_num
  have hCP : 16 ≤ Nat.card ↥CP := by norm_num at h128; omega

  have hr4 : Nat.card ↥CV ≤ Nat.card ↥f.range := by
    have hk := hfk.trans hcV
    have hr := hfrc.trans hcV
    rw [← hfc] at hCP
    set m := Nat.card ↥f.range
    interval_cases m <;> omega
  have heq : f.range = CV := Subgroup.eq_of_le_of_card_ge hfr hr4
  have hzCV : z ∈ CV := by
    refine ⟨ι.z_mem_V_F4, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := ι.z_comm_F4 hyT
    exact h.symm
  rw [← heq] at hzCV
  obtain ⟨p, hpz⟩ := hzCV
  exact ⟨p, ⟨ι.P_le_T_F4 (p : ↥CP).2.1, (p : ↥CP).2.2⟩, hpz⟩

theorem card_cent_le_F4 {y : G} (hyT : y ∈ T) (hyL : y ∈ L) (hy2 : y * y = 1)
    (hyP : y ∉ pCoreOf 2 L) (hyU : y ∉ fsuU T V) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) ≤ 2 ^ 7 ∧
      (2 ^ 7 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) →
        ∃ s ∈ T ⊓ Subgroup.centralizer ({y} : Set G), s * s = z) := by
  obtain ⟨θ, -, -, hker, -, -, -, hQv⟩ := ι.exists_coordZ_F4 ι.hyp
  by_cases hR : θ ⟨y, hyL⟩ ∈ Qv (vE (ZMod 2) 0)
  · obtain ⟨u, huU, hθu⟩ := hQv _ hR
    have hp : y * (u : G)⁻¹ ∈ pCoreOf 2 L := by
      have h : θ (⟨y, hyL⟩ * u⁻¹) = 1 := by rw [map_mul, map_inv, hθu, mul_inv_cancel]
      exact (hker _).mp h
    obtain ⟨h1, h2⟩ := ι.card_cent_le_of_mem_F4 hyT hy2 hyP hyU hp huU (by group)
    exact ⟨h1, fun _ => ⟨d, h2, ι.d_sq⟩⟩
  · exact ι.card_cent_le_of_not_mem_F4 hker hQv hyT hyL hyP hR

end Inv_F4

end L14333

end CFSG.Quasithin.H13

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GLayer

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def L34GPocketComm (G : Type) [Group G] : Prop :=
  ∀ (x : G) (X : Subgroup G) (y : G) (K : Subgroup G), Sec3PocketData x X y K →
    ⁅K, fstarLayer y⁆ = ⊥

@[expose] def L34GLemmaA (G : Type) [Group G] : Prop :=
  ∀ (v y : G) (D K' : Subgroup G), Sec3PocketData v D y K' → v ∉ fstarLayer y ⊔ zpowers y

theorem l34g_pocketComm_of_inputs (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hS : Asc82SchurU43) {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}
    (hSet : Sec3SettingLB G t L) : L34GPocketComm G :=
  fun _ _ _ _ hD => sec3_pocket_comm_fstarLayer hT2 hC1 hS hSet hD

theorem l34g_lemmaA_of_inputs (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hS : Asc82SchurU43) (hCor : Asc82CorIII) {G : Type} [Group G] [Finite G] {t : G}
    {L : Subgroup G} (hSet : Sec3SettingLB G t L) : L34GLemmaA G :=
  fun _ _ _ _ hD => sec3_pocket_not_mem_fstarLayer hT2 hC1 hS hCor hSet hD

end CFSG.OddStandard.SmallF3.Omega

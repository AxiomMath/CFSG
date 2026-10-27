module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data0
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data1
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data2
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data3
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data4
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data5
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data6
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data7
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.FixedLine M CFSG.KC.BM.Twin.xorRows 2412792 15848443123629662499 C0.rows C1.rows C2.rows C3.rows C4.rows C5.rows C6.rows C7.rows C8.rows C9.rows C10.rows C11.rows C12.rows C13.rows C14.rows C15.rows C16.rows C17.rows C18.rows C19.rows C20.rows C21.rows C22.rows C23.rows C24.rows C25.rows
#kc_eval CFSG.KC.BM.FixedLine M CFSG.KC.BM.Twin.stripsOf 4371 2412792 6511502472225482976 M.rows
#kc_eval CFSG.KC.BM.FixedLine PM CFSG.KC.BM.Twin.rank 4371 2412792 7515152030086619891 M.rows 0 1
#kc_eval CFSG.KC.BM.FixedLine QM CFSG.KC.BM.Twin.polyMul 4371 2412792 10731731060959630006 PM M 0 1
#kc_eval CFSG.KC.BM.FixedLine R CFSG.KC.BM.Twin.mtStrips 4371 4371 2412792 5827869548903466217
#kc_eval CFSG.KC.BM.FixedLine RC CFSG.KC.BM.Twin.prod 4371 2412792 10107467917185154277 R C25
#kc_eval CFSG.KC.BM.FixedLine Mp CFSG.KC.BM.Twin.xorStrips 4371 2412792 3610187261574347447 M RC R
#kc_eval CFSG.KC.BM.FixedLine Mpi CFSG.KC.BM.Twin.inv 4371 2412792 4127382055694078119 Mp
#kc_eval CFSG.KC.BM.FixedLine PQ0 CFSG.KC.BM.Twin.rank 4370 2412240 16671695310579195808 Q0.rows 1 1
#kc_eval CFSG.KC.BM.FixedLine QQ0 CFSG.KC.BM.Twin.polyMul 4370 2412240 5701622186625041724 PQ0 CFSG.KC.BM.NativePair.Q0 1 1
#kc_eval CFSG.KC.BM.FixedLine PQ25 CFSG.KC.BM.Twin.rank 4370 2412240 1705239109284927524 Q25.rows 1 1
#kc_eval CFSG.KC.BM.FixedLine QQ25 CFSG.KC.BM.Twin.polyMul 4370 2412240 5863692081585550021 PQ25 CFSG.KC.BM.NativePair.Q25 1 1
